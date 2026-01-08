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

import tools.aqua.wvm.language.Assignment
import tools.aqua.wvm.language.Fail
import tools.aqua.wvm.language.Havoc
import tools.aqua.wvm.language.Swap

sealed interface RDFact : Fact {
  fun varname(): String
}

data class RDInitFact(val varname: String) : RDFact {
  override fun varname() = varname

  override fun toString(): String = "($varname, ?)"
}

data class RDWriteFact(val varname: String, val node: CFGNode<*>) : RDFact {
  override fun varname() = varname

  override fun toString(): String = "($varname, ${node.id})"
}

fun unitialized(node: CFGNode<*>, marking: Map<CFGNode<*>, InOut<RDFact>>) =
    marking[node]!!.first.filter { it is RDInitFact }.map { it.varname() }.toSet()

val RDAnalysis =
    DataflowAnalysis<RDFact>(
        direction = Direction.Forward,
        type = AnalysisType.May,
        initialization = { c, s ->
          c.nodes().associateWith { node ->
            Pair<Set<RDFact>, Set<RDFact>>(
                if (!c.initial().contains(node)) emptySet()
                else varsInCFG(c).map { RDInitFact(it) }.toSet(),
                emptySet())
          }
        },
        assignGen = { node, _ ->
          val vrs = varsInExpr(node.stmt.addr)
          vrs.map { RDWriteFact(it, node) }.toSet()
        },
        assignKill = { fact, node -> varsInExpr(node.stmt.addr).contains(fact.varname()) },
        swapGen = { node, _ ->
          val vrs = varsInExpr(node.stmt.left) + varsInExpr(node.stmt.right)
          vrs.map { RDWriteFact(it, node) }.toSet()
        },
        swapKill = { fact, node -> varsInStmt(node.stmt).contains(fact.varname()) },
        havocGen = { node, _ ->
          val vrs = varsInExpr(node.stmt.addr)
          vrs.map { RDWriteFact(it, node) }.toSet()
        },
        havocKill = { fact, node -> varsInStmt(node.stmt).contains(fact.varname()) },
        check =
            Check { cfg, marking ->
              val unitialized =
                  cfg.nodes().associateWith { node ->
                    unitialized(node, marking)
                        .intersect(
                            when (node.stmt) {
                              is Assignment -> varsInExpr(node.stmt.expr)
                              is Fail -> emptySet()
                              is Havoc -> emptySet()
                              else -> varsInStmt(node.stmt)
                            })
                  }

              if (unitialized.none { it.value.isNotEmpty() }) {
                "Reaching definitions check OK: No uninitialized variables are read"
              } else {
                val rdInfo =
                    unitialized
                        .filter { it.value.isNotEmpty() }
                        .map { "${cfg.idOf(it.key)} reads ${it.value.joinToString(", ")}" }
                        .sorted()
                "Reaching definitions check FAILED: $rdInfo"
              }
            })

object RDGenKill {
  fun gen(node: CFGNode<*>): Set<String> =
      when (val stmt = node.stmt) {
        is Assignment -> varsInExpr(stmt.addr).map { RDWriteFact(it, node).toString() }.toSet()
        is Swap ->
            (varsInExpr(stmt.left) + varsInExpr(stmt.right))
                .map { RDWriteFact(it, node).toString() }
                .toSet()
        is Havoc -> varsInExpr(stmt.addr).map { RDWriteFact(it, node).toString() }.toSet()
        else -> emptySet()
      }

  fun kill(node: CFGNode<*>): Set<String> =
      when (val stmt = node.stmt) {
        is Assignment -> varsInExpr(stmt.addr)
        is Swap -> varsInExpr(stmt.left) + varsInExpr(stmt.right)
        is Havoc -> varsInExpr(stmt.addr)
        else -> emptySet()
      }
}
