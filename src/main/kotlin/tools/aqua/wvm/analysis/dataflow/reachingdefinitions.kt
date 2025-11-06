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

sealed interface RDFact : Fact {
  fun varname(): String
}

data class RDInitFact(val varname: String, val init: Boolean) : RDFact {
  override fun varname() = varname

  override fun toString(): String = "($varname, ${if (init) "init" else "?"})"
}

data class RDWriteFact(val varname: String, val node: CFGNode<*>) : RDFact {
  override fun varname() = varname

  override fun toString(): String = "($varname, write)"
}

data class RDHavocFact(val varname: String, val node: CFGNode<*>) : RDFact {
  override fun varname() = varname

  override fun toString(): String = "($varname, havoc)"
}

val RDAnalysis =
    DataflowAnalysis(
        direction = Direction.Forward,
        type = AnalysisType.May,
        initialization = { c, s ->
          c.nodes().associateWith { node ->
            Pair(
                if (!c.initial().contains(node)) emptySet()
                else varsInCFG(c).map { RDInitFact(it, s.getNames().contains(it)) }.toSet(),
                emptySet())
          }
        },
        assignGen = { node ->
          val vrs = varsInExpr(node.stmt.addr)
          vrs.map { RDWriteFact(it, node) }.toSet()
        },
        assignKill = { fact, node -> varsInStmt(node.stmt).contains(fact.varname()) },
        swapGen = { node ->
          val vrs = varsInExpr(node.stmt.left) + varsInExpr(node.stmt.right)
          vrs.map { RDWriteFact(it, node) }.toSet()
        },
        swapKill = { fact, node -> varsInStmt(node.stmt).contains(fact.varname()) },
        havocGen = { node ->
          val vrs = varsInExpr(node.stmt.addr)
          vrs.map { RDHavocFact(it, node) }.toSet()
        },
        havocKill = { fact, node -> varsInStmt(node.stmt).contains(fact.varname()) })
