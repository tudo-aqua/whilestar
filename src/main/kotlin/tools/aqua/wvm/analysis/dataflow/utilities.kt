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

fun varsInExpr(expr: Expression<*>): Set<String> =
    when (expr) {
      is ValAtAddr -> varsInExpr(expr.addr)
      is Variable -> setOf(expr.name)
      is DeRef -> varsInExpr(expr.reference)
      is ArrayAccess -> varsInExpr(expr.array) + varsInExpr(expr.index)
      is VarAddress -> setOf(expr.variable.name)
      is NumericLiteral -> emptySet()
      is Add -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Sub -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Rem -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Mul -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Div -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Gt -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Lt -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Gte -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Lte -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Eq -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is And -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Or -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Imply -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Equiv -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Not -> varsInExpr(expr.negated)
      is UnaryMinus -> varsInExpr(expr.negated)
      is True -> emptySet()
      is False -> emptySet()
      // Verification Expressions should not be reachable for the data flow analysis
      else -> error("Unsupported expression for dataflow analysis: $expr ${expr::class}")
    }

fun varsInStmt(stmt: Statement): Set<String> =
    when (stmt) {
      is IfThenElse -> varsInExpr(stmt.cond) + varsInSeq(stmt.thenBlock) + varsInSeq(stmt.elseBlock)
      is While -> varsInExpr(stmt.head) + varsInSeq(stmt.body) + varsInExpr(stmt.invariant)
      is Assignment -> varsInExpr(stmt.addr) + varsInExpr(stmt.expr)
      is Fail -> emptySet()
      is Havoc -> varsInExpr(stmt.addr)
      is Swap -> varsInExpr(stmt.left) + varsInExpr(stmt.right)
      is Print -> stmt.values.flatMap { varsInExpr(it) }.toSet()
      is Assertion -> varsInExpr(stmt.cond)
    }

fun varsInSeq(seq: SequenceOfStatements): Set<String> =
    seq.statements.flatMap { varsInStmt(it) }.toSet()

fun varsInCFG(cfg: CFG): Set<String> = cfg.nodes().flatMap { varsInStmt(it.stmt) }.toSet()
