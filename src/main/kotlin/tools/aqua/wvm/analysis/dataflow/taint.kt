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
import tools.aqua.wvm.language.Havoc
import tools.aqua.wvm.language.Print
import tools.aqua.wvm.language.Swap

data class TaintFact(val varname: String) : Fact {
  override fun toString(): String = "$varname"
}

val TaintAnalysis =
    DataflowAnalysis(
        direction = Direction.Forward,
        type = AnalysisType.May,
        initialization = { cfg, _ ->
          cfg.nodes()
              .associateWith { Pair(emptySet<TaintFact>(), emptySet<TaintFact>()) }
              .toMutableMap()
        },
        havocKill = { fact, node -> varsInStmt(node.stmt).contains(fact.varname) },
        havocGen = { node, _ ->
          val vrs = varsInStmt(node.stmt)
          vrs.map { TaintFact(it) }.toSet()
        },
        assignKill = { fact, node -> varsInExpr(node.stmt.addr).contains(fact.varname) },
        assignGen = { node, inflow ->
          if (inflow.map { it.varname }.toSet().intersect(varsInExpr(node.stmt.expr)).isEmpty())
              emptySet<TaintFact>()
          else varsInExpr(node.stmt.addr).map { TaintFact(it) }.toSet()
        },
        swapKill = { fact, node -> varsInStmt(node.stmt).contains(fact.varname) },
        swapGen = { node, inflow ->
          val set1 =
              if (inflow
                  .map { it.varname }
                  .toSet()
                  .intersect(varsInExpr(node.stmt.right))
                  .isEmpty())
                  emptySet<TaintFact>()
              else varsInExpr(node.stmt.left).map { TaintFact(it) }.toSet()
          val set2 =
              if (inflow.map { it.varname }.toSet().intersect(varsInExpr(node.stmt.left)).isEmpty())
                  emptySet<TaintFact>()
              else varsInExpr(node.stmt.right).map { TaintFact(it) }.toSet()
          set1.union(set2)
        },
        check =
            Check { cfg, marking ->
              val taintedPrints =
                  marking
                      .filter { (node, taint) ->
                        node.stmt is Print &&
                            taint.first.any { varsInStmt(node.stmt).contains(it.varname) }
                      }
                      .entries

              if (taintedPrints.isEmpty()) {
                "Taint check OK: No external input reaches a print"
              } else {
                val taintFlow =
                    taintedPrints
                        .map { "${cfg.idOf(it.key)} by ${it.value.first.joinToString(", ")}" }
                        .sorted()
                "Taint check FAILED: The following statements are reachable by taint: $taintFlow"
              }
            })

object TaintGenKill {
  fun gen(node: CFGNode<*>, inflow: Set<TaintFact>): Set<String> =
      when (val stmt = node.stmt) {
        is Havoc -> varsInExpr(stmt.addr)
        is Assignment -> {
          val taintedVars = inflow.map { it.varname }.toSet()
          if (varsInExpr(stmt.expr).intersect(taintedVars).isNotEmpty()) {
            varsInExpr(stmt.addr)
          } else {
            emptySet()
          }
        }
        is Swap -> {
          val taintedVars = inflow.map { it.varname }.toSet()
          val genSet = mutableSetOf<String>()
          if (varsInExpr(stmt.right).intersect(taintedVars).isNotEmpty()) {
            genSet.addAll(varsInExpr(stmt.left))
          }
          if (varsInExpr(stmt.left).intersect(taintedVars).isNotEmpty()) {
            genSet.addAll(varsInExpr(stmt.right))
          }
          genSet
        }
        else -> emptySet()
      }

  fun kill(node: CFGNode<*>, inflow: Set<TaintFact>): Set<String> =
      when (val stmt = node.stmt) {
        is Assignment -> varsInExpr(stmt.addr)
        is Swap -> varsInExpr(stmt.left) + varsInExpr(stmt.right)
        else -> emptySet()
      }
}
