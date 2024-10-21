/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2024 The While* Authors
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

package tools.aqua.wvm.analysis.hoare

import java.math.BigInteger
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.machine.Scope

class WPCProofSystem(val context: Context, val output: Output) {

  private var uniqueId = 0

  private fun vcgen(
      pre: BooleanExpression,
      program: List<Statement>,
      post: BooleanExpression
  ): List<Entailment> =
      listOf(Entailment(pre, wpc(SequenceOfStatements(program), post), "Precondition")) +
          vcgen(SequenceOfStatements(program), post)

  private fun vcgen(stmt: Statement, post: BooleanExpression): List<Entailment> =
      when (stmt) {
        is While ->
            listOf(
                Entailment(
                    And(stmt.invariant, stmt.head),
                    wpc(stmt.body, stmt.invariant),
                    "Entering loop with invariant ${stmt.invariant}"),
                Entailment(
                    And(stmt.invariant, Not(stmt.head)),
                    post,
                    "Leaving loop with invariant ${stmt.invariant}")) +
                vcgen(stmt.body, stmt.invariant)
        is IfThenElse -> vcgen(stmt.thenBlock, post) + vcgen(stmt.elseBlock, post)
	is Assertion -> listOf(Entailment(stmt.cond, post, "Following assertion"))
        else -> emptyList()
      }

  private fun vcgen(stmt: SequenceOfStatements, post: BooleanExpression): List<Entailment> =
      if (stmt.isExhausted()) emptyList()
      else {
        val last = stmt.end()
        val wpc = wpc(last, post)
        vcgen(last, post) + vcgen(SequenceOfStatements(stmt.front()), wpc)
      }

  private fun wpc(stmt: Statement, post: BooleanExpression): BooleanExpression =
      when (stmt) {
        is While -> stmt.invariant
        is IfThenElse ->
            And(
                Imply(stmt.cond, wpc(stmt.thenBlock, post)),
                Imply(Not(stmt.cond), wpc(stmt.elseBlock, post)))
        is Assignment -> wpc(stmt, post)
        is Swap -> wpc(stmt, post)
	is Assertion -> stmt.cond
        is Print -> post
        is Fail -> True
        is Havoc -> wpc(stmt, post)
      }

  private fun wpc(stmt: Assignment, post: BooleanExpression): BooleanExpression =
      when (stmt.addr) {
        is Variable -> replace(post, stmt.addr, stmt.expr)
        else -> throw Exception("expression (${stmt.addr}) not supported by proof system.")
      }

  private fun wpc(stmt: Swap, post: BooleanExpression): BooleanExpression {
    if (stmt.left !is Variable) {
      throw Exception("expression (${stmt.left}) not supported by proof system.")
    }
    if (stmt.right !is Variable) {
      throw Exception("expression (${stmt.right}) not supported by proof system.")
    }
    val tVar = Variable("****") // no real variable can have this name
    val temp1 = replace(post, stmt.left, ValAtAddr(tVar))
    val temp2 = replace(temp1, stmt.right, ValAtAddr(stmt.left))
    return replace(temp2, tVar, ValAtAddr(stmt.right))
  }

  private fun wpc(stmt: Havoc, post: BooleanExpression): BooleanExpression {
    if (stmt.addr !is Variable) {
      throw Exception("expression (${stmt.addr}) not supported by proof system.")
    }
    val boundVar = Variable("${stmt.addr}${uniqueId++}")
    return Forall(
        boundVar,
        Or(
            Or(
                Lt(ValAtAddr(boundVar), NumericLiteral(stmt.lower)),
                Gte(ValAtAddr(boundVar), NumericLiteral(stmt.upper))),
            replace(post, stmt.addr, ValAtAddr(boundVar))))
  }

  private fun wpc(stmt: SequenceOfStatements, post: BooleanExpression): BooleanExpression =
      if (stmt.isExhausted()) post
      else wpc(SequenceOfStatements(stmt.front()), wpc(stmt.end(), post))

  private fun replace(
      phi: ArithmeticExpression,
      v: Variable,
      replacement: ArithmeticExpression
  ): ArithmeticExpression =
      when (phi) {
        is ValAtAddr -> if (phi.addr is Variable && phi.addr.name == v.name) replacement else phi
        is NumericLiteral -> NumericLiteral(phi.literal)
        is UnaryMinus -> UnaryMinus(replace(phi.negated, v, replacement))
        is Add -> Add(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Sub -> Sub(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Mul -> Mul(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Div -> Div(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Rem -> Rem(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is VarAddress -> throw Exception("expression ($phi) not supported by proof system.")
      }

  private fun replace(
      phi: BooleanExpression,
      v: Variable,
      replacement: ArithmeticExpression
  ): BooleanExpression =
      when (phi) {
        is True -> phi
        is False -> phi
        is Not -> Not(replace(phi.negated, v, replacement))
        is Eq ->
            Eq(replace(phi.left, v, replacement), replace(phi.right, v, replacement), phi.nesting)
        is Gt -> Gt(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Gte -> Gte(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Lt -> Lt(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Lte -> Lte(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is And -> And(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Equiv -> Equiv(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Imply -> Imply(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        is Or -> Or(replace(phi.left, v, replacement), replace(phi.right, v, replacement))
        // since bound vars are never program vars, we only need to replace on expression
        is Forall -> Forall(phi.boundVar, replace(phi.expression, v, replacement))
      }

  fun augment(pre: BooleanExpression, scope: Scope): BooleanExpression {
    var newPre = pre
    scope.symbols
        .filter { it.value.size == 1 && it.value.type == BasicType.INT }
        .map { Eq(ValAtAddr(Variable(it.key)), NumericLiteral(BigInteger.ZERO), 0) }
        .forEach { newPre = And(newPre, it) }
    return newPre
  }

  fun proof(): Boolean {
    val pre = augment(context.pre, context.scope)
    val vcs = vcgen(pre, context.program, context.post)
    output.println("==== generating verification conditions: ====")
    var success = true
    vcs.forEach { output.println("$it") }
    for (vc in vcs) {
      output.println("---------------------------------------------")
      output.println("${vc.explanation}:")
      val expr = vc.smtTest()
      output.println("SMT Test: $expr")
      val solver = SMTSolver()
      val result = solver.solve(vc.smtTest())
      success = success and (result.status == SatStatus.UNSAT)
      output.println(
          when (result.status) {
            SatStatus.UNSAT -> "successful."
            SatStatus.SAT -> "counterexample: ${result.model}"
            SatStatus.UNKNOWN -> "could not be decided.."
            SatStatus.PENDING -> "error during solving."
          })

      if (result.status != SatStatus.UNSAT) {
        success = false
      }
    }
    output.println("=============================================")
    output.println("The proof was ${if (success) "" else "not"} successful.")
    return success
  }
}
