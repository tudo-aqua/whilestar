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
      is NumericLiteral -> emptySet()
      is Add -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Sub -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Gt -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Lt -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Gte -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is Lte -> varsInExpr(expr.left) + varsInExpr(expr.right)
      is BooleanExpression ->
          error("This Boolean expression is not supported yet $expr ${expr::class}") // TODO!!!
      else -> error("Unsupported expression for dataflow analysis: $expr")
    }

fun varsInStmt(stmt: Statement): Set<String> =
    when (stmt) {
      is IfThenElse -> varsInExpr(stmt.cond) + varsInSeq(stmt.thenBlock) + varsInSeq(stmt.elseBlock)
      is While -> varsInExpr(stmt.head) + varsInSeq(stmt.body) // todo: invariant?
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
