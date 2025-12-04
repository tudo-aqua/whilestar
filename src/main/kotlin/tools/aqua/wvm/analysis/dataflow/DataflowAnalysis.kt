/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2025 The While* Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package tools.aqua.wvm.analysis.dataflow

import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Scope

enum class Direction {
  Forward,
  Backward
}

enum class AnalysisType {
  Must /* Intersection*/,
  May /* Union */
}

typealias FactSet<F> = Set<F>

typealias InOut<F> = Pair<FactSet<F>, FactSet<F>>

typealias Marking<F> = Map<CFGNode<*>, InOut<F>>

typealias AnalysisLog<F> = List<Marking<F>>

interface Fact

fun interface Kill<F : Fact, T : Statement> {
  fun kill(fact: F, node: CFGNode<T>): Boolean
}

fun interface Gen<F : Fact, T : Statement> {
  fun gen(node: CFGNode<T>, inflow: FactSet<F>): Set<F>
}

fun interface Initialization<F : Fact> {
  fun initialize(cfg: CFG, scope: Scope): Marking<F>
}

fun interface Check<F : Fact> {
  fun check(cfg: CFG, marking: Marking<F>): String
}

data class DataflowAnalysis<F : Fact>(
    val direction: Direction,
    val type: AnalysisType,
    val initialization: Initialization<F>,
    val ifGen: Gen<F, IfThenElse> = Gen { _, _ -> emptySet() },
    val ifKill: Kill<F, IfThenElse> = Kill { _, _ -> false },
    val whileGen: Gen<F, While> = Gen { _, _ -> emptySet() },
    val whileKill: Kill<F, While> = Kill { _, _ -> false },
    val assignGen: Gen<F, Assignment> = Gen { _, _ -> emptySet() },
    val assignKill: Kill<F, Assignment> = Kill { _, _ -> false },
    val failGen: Gen<F, Fail> = Gen {_, _ -> emptySet() },
    val failKill: Kill<F, Fail> = Kill { _, _ -> false },
    val havocGen: Gen<F, Havoc> = Gen { _, _ -> emptySet() },
    val havocKill: Kill<F, Havoc> = Kill { _, _ -> false },
    val swapGen: Gen<F, Swap> = Gen { _, _ -> emptySet() },
    val swapKill: Kill<F, Swap> = Kill { _, _ -> false },
    val printGen: Gen<F, Print> = Gen { _, _ -> emptySet() },
    val printKill: Kill<F, Print> = Kill { _, _ -> false },
    val assertionGen: Gen<F, Assertion> = Gen { _, _ -> emptySet() },
    val assertionKill: Kill<F, Assertion> = Kill { _, _ -> false },
    private val check: Check<F> = Check { _, _ -> "ERROR: Check not available for this analysis" }
) {

  fun initialize(cfg: CFG, scope: Scope): Marking<F> = initialization.initialize(cfg, scope)

  @Suppress("UNCHECKED_CAST")
  fun next(cfg: CFG, marking: Marking<F>): Marking<F> {
    return cfg.nodes().associateWith { node ->
      val preds = if (direction == Direction.Forward) cfg.pred(node) else cfg.succ(node)
      val inFacts: Set<F> =
          when (type) {
            AnalysisType.May ->
                preds
                    .flatMap {
                      if (direction == Direction.Forward) marking[it]!!.second
                      else marking[it]!!.first
                    }
                    .toSet()
            AnalysisType.Must ->
                if (preds.isEmpty()) emptySet()
                else {
                  val init =
                      if (direction == Direction.Forward) marking[preds.first()]!!.second
                      else marking[preds.first()]!!.first
                  preds.drop(1).fold(init) { acc, n ->
                    acc.intersect(
                        if (direction == Direction.Forward) marking[n]!!.second
                        else marking[n]!!.first)
                  }
                }
          } + if (direction == Direction.Forward) marking[node]!!.first else marking[node]!!.second
      val outFacts =
          when (node.stmt) {
            is IfThenElse ->
              (inFacts.filter { !ifKill.kill(it, node as CFGNode<IfThenElse>) } +
                        ifGen.gen(node as CFGNode<IfThenElse>, marking[node]!!.first))
                    .toSet()
            is While ->
                (inFacts.filter { !whileKill.kill(it, node as CFGNode<While>) } +
                        whileGen.gen(node as CFGNode<While>, marking[node]!!.first))
                    .toSet()
            is Assignment ->
                (inFacts.filter { !assignKill.kill(it, node as CFGNode<Assignment>) } +
                        assignGen.gen(node as CFGNode<Assignment>, marking[node]!!.first))
                    .toSet()
            is Fail ->
                (inFacts.filter { !failKill.kill(it, node as CFGNode<Fail>) } +
                        failGen.gen(node as CFGNode<Fail>, marking[node]!!.first))
                    .toSet()
            is Havoc ->
                (inFacts.filter { !havocKill.kill(it, node as CFGNode<Havoc>) } +
                        havocGen.gen(node as CFGNode<Havoc>, marking[node]!!.first))
                    .toSet()
            is Print ->
                (inFacts.filter { !printKill.kill(it, node as CFGNode<Print>) } +
                        printGen.gen(node as CFGNode<Print>, marking[node]!!.first))
                    .toSet()
            is Swap ->
                (inFacts.filter { !swapKill.kill(it, node as CFGNode<Swap>) } +
                        swapGen.gen(node as CFGNode<Swap>, marking[node]!!.first))
                    .toSet()
            is Assertion ->
                (inFacts.filter { !assertionKill.kill(it, node as CFGNode<Assertion>) } +
                        assertionGen.gen(node as CFGNode<Assertion>, marking[node]!!.first))
                    .toSet()
          }

      if (direction == Direction.Forward) Pair(inFacts, outFacts) else Pair(outFacts, inFacts)
    }
  }

  fun isFixedPoint(cfg: CFG, marking: Marking<F>): Boolean =
      next(cfg, marking).all { (n, f) -> f == marking[n] }

  fun execute(cfg: CFG, scope: Scope): AnalysisLog<F> {
    val log = mutableListOf<Marking<F>>()
    var currentMarking = this.initialize(cfg, scope)
    log.add(currentMarking)

    while (true) {
      val nextMarking = this.next(cfg, currentMarking)
      if (nextMarking == currentMarking) {
        break
      }
      currentMarking = nextMarking
      log.add(currentMarking)
    }

    return log.toList()
  }

  fun check(cfg: CFG, marking: Marking<F>): String = check.check(cfg, marking)
}
