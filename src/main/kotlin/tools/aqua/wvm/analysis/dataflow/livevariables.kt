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

import tools.aqua.wvm.language.Assertion
import tools.aqua.wvm.language.Assignment
import tools.aqua.wvm.language.Havoc
import tools.aqua.wvm.language.IfThenElse
import tools.aqua.wvm.language.Print
import tools.aqua.wvm.language.Statement
import tools.aqua.wvm.language.Swap
import tools.aqua.wvm.language.While

class LVFact(val varname: String, val node: CFGNode<*>) : Fact {
  override fun hashCode(): Int = varname.hashCode()

  override fun equals(other: Any?): Boolean = other is LVFact && other.varname == varname

  override fun toString(): String = varname

}

val LVAnalysis =
    DataflowAnalysis(
        direction = Direction.Backward,
        type = AnalysisType.May,
        initialization = { c, s ->
          c.nodes().associateWith { node -> Pair(emptySet(), emptySet()) }
        },
        assignGen = { node -> varsInExpr(node.stmt.expr).map { LVFact(it, node) }.toSet() },
        assignKill = { fact, node -> varsInExpr(node.stmt.addr).contains(fact.varname) },
        swapGen = {node -> (varsInExpr(node.stmt.left) + varsInExpr(node.stmt.right)).map{ LVFact(it, node)}.toSet() },
        swapKill = { fact, node ->
          varsInExpr(node.stmt.left).contains(fact.varname) ||
              varsInExpr(node.stmt.right).contains(fact.varname)
        },
        havocKill = { fact, node -> varsInExpr(node.stmt.addr).contains(fact.varname) },
        printGen = { node ->
          node.stmt.values.map { varsInExpr(it) }.flatten().map { LVFact(it, node) }.toSet()
        },
        whileGen = { node -> varsInExpr(node.stmt.head).map { LVFact(it, node) }.toSet() },
        ifGen = { node -> varsInExpr(node.stmt.cond).map { LVFact(it, node) }.toSet() },
        assertionGen = {node -> varsInExpr(node.stmt.cond).map { LVFact(it, node) }.toSet() },
    )

object LVGenKill {
    fun gen(stmt: Statement): Set<String> = when (stmt) {
        is Assignment -> varsInExpr(stmt.expr)
        is Print -> stmt.values.map { varsInExpr(it) }.flatten().toSet()
        is While -> varsInExpr(stmt.head)
        is IfThenElse -> varsInExpr(stmt.cond)
        is Assertion -> varsInExpr(stmt.cond)
        is Swap -> varsInExpr(stmt.left) + varsInExpr(stmt.right)
        else -> emptySet()
    }

    fun kill(stmt: Statement): Set<String> = when (stmt) {
        is Assignment -> varsInExpr(stmt.addr)
        is Swap -> varsInExpr(stmt.left) + varsInExpr(stmt.right)
        is Havoc -> varsInExpr(stmt.addr)
        else -> emptySet()

    }
}