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
import tools.aqua.wvm.analysis.VerificationApproach
import tools.aqua.wvm.analysis.VerificationResult
import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.machine.Scope

class WPCProofSystem(
    override val context: Context,
    override val out: Output,
    override val verbose: Boolean = false,
) : VerificationApproach {
  override val name: String = "WPC Proof System"
  private var uniqueId = 0

  private fun vcgen(
      pre: BooleanExpression,
      program: List<Statement>,
      post: BooleanExpression
  ): Pair<BooleanExpression, List<Entailment>> {
    val l1 = listOf(Entailment(pre, wpc(SequenceOfStatements(program), post), "Precondition"))
    val (newPre, l2) = vcgen(pre, SequenceOfStatements(program), post)
    return Pair(newPre, l1 + l2)
  }

  private fun vcgen(
      pre: BooleanExpression,
      stmt: Statement,
      post: BooleanExpression
  ): Pair<BooleanExpression, List<Entailment>> =
      when (stmt) {
        is While -> {
          val wpcBody = wpc(stmt.body, prepare(stmt.invariant))
          val assumption = And(pre, prepare(stmt.invariant))
          val (_, vcsBody) =
              vcgen(And(assumption, prepare(stmt.head)), stmt.body, prepare(stmt.invariant))
          Pair(
              And(assumption, prepare(Not(stmt.head))),
              listOf(
                  Entailment(
                      And(assumption, prepare(stmt.head)),
                      wpcBody,
                      "Entering loop with invariant ${stmt.invariant}"),
                  Entailment(
                      And(assumption, prepare(Not(stmt.head))),
                      post,
                      "Leaving loop with invariant ${stmt.invariant}")) + vcsBody)
        }
        is IfThenElse -> {
          val (_, vcs1) = vcgen(pre, stmt.thenBlock, post)
          val (_, vcs2) = vcgen(pre, stmt.elseBlock, post)
          Pair(pre, vcs1 + vcs2)
        }
        is Assertion ->
            Pair(
                And(pre, prepare(stmt.cond)),
                listOf(Entailment(And(pre, prepare(stmt.cond)), post, "Following assertion")))
        else -> Pair(pre, emptyList())
      }

  private fun vcgen(
      pre: BooleanExpression,
      stmt: SequenceOfStatements,
      post: BooleanExpression
  ): Pair<BooleanExpression, List<Entailment>> =
      if (stmt.isExhausted()) Pair(pre, emptyList())
      else {
        val last = stmt.end()
        val wpc = wpc(last, post)
        val (newPre1, l1) = vcgen(pre, SequenceOfStatements(stmt.front()), wpc)
        val (newPre2, l2) = vcgen(newPre1, last, post)
        Pair(newPre2, l1 + l2)
      }

  private fun wpc(stmt: Statement, post: BooleanExpression): BooleanExpression =
      when (stmt) {
        is While -> prepare(stmt.invariant)
        is IfThenElse ->
            And(
                Imply(prepare(stmt.cond), wpc(stmt.thenBlock, post)),
                Imply(Not(prepare(stmt.cond)), wpc(stmt.elseBlock, post)))
        is Assignment -> wpc(stmt, post)
        is Swap -> wpc(stmt, post)
        is Assertion -> And(prepare(stmt.cond), post)
        is Print -> post
        is Fail -> True
        is Havoc -> wpc(stmt, post)
      }

  private fun wpc(stmt: Assignment, post: BooleanExpression): BooleanExpression =
      when (stmt.addr) {
        is Variable -> replace(post, stmt.addr, prepare(stmt.expr))
        is DeRef ->
            replaceM(
                post,
                ArrayWrite(AnyArray, ValAtAddr(prepare(stmt.addr.reference)), prepare(stmt.expr)))
        is ArrayAccess ->
            replaceM(
                post,
                ArrayWrite(
                    AnyArray,
                    Add(prepare(stmt.addr.array), prepare(stmt.addr.index)),
                    prepare(stmt.expr)))
        else -> throw Exception("this case is not supposed to be reachable: replaceM wpc of $stmt")
      }

  private fun wpc(stmt: Swap, post: BooleanExpression): BooleanExpression {
    val tVar = Variable("tmp_${uniqueId++}")
    val leftToTmp = Assignment(tVar, ValAtAddr(stmt.left))
    val rightToLeft = Assignment(stmt.left, ValAtAddr(stmt.right))
    val tmpToRight = Assignment(stmt.right, ValAtAddr(tVar))
    return wpc(leftToTmp, wpc(rightToLeft, wpc(tmpToRight, post)))
  }

  private fun wpc(stmt: Havoc, post: BooleanExpression): BooleanExpression {
    val boundVar = Variable("ext_${uniqueId++}") // TODO: truly unique variable names!
    val wpcInner =
        when (stmt.addr) {
          is Variable -> replace(post, stmt.addr, ValAtAddr(boundVar))
          is DeRef ->
              replaceM(
                  post,
                  ArrayWrite(
                      AnyArray, ValAtAddr(prepare(stmt.addr.reference)), ValAtAddr(boundVar)))
          is ArrayAccess ->
              replaceM(
                  post,
                  ArrayWrite(
                      AnyArray,
                      Add(prepare(stmt.addr.array), prepare(stmt.addr.index)),
                      ValAtAddr(boundVar)))
          else ->
              throw Exception("this case is not supposed to be reachable: replaceM wpc of $stmt")
        }
    return Forall(
        boundVar,
        Or(
            Or(
                Lt(ValAtAddr(boundVar), NumericLiteral(stmt.lower)),
                Gte(ValAtAddr(boundVar), NumericLiteral(stmt.upper))),
            wpcInner))
  }

  private fun wpc(stmt: SequenceOfStatements, post: BooleanExpression): BooleanExpression {
    println(post)
    return if (stmt.isExhausted()) post
    else wpc(SequenceOfStatements(stmt.front()), wpc(stmt.end(), post))
  }

  // {Q[M(y) / x]} x := *y; {Q}
  private fun prepare(phi: AddressExpression): AddressExpression =
      when (phi) {
        is Variable -> phi
        is DeRef -> ArrayRead(AnyArray, ValAtAddr(prepare(phi.reference)))
        is ArrayAccess -> ArrayRead(AnyArray, Add(prepare(phi.array), prepare(phi.index)))
        // we introduce array expressions only in the wpc, other case cannot occur
        else -> throw Exception("this case should not occur. $phi")
      // is ArrayWrite -> ValAtAddr(ArrayWrite(phi.array, replace(phi.index, v, replacement),
      // replace(phi.value, v, replacement)))
      // is AnyArray -> throw Exception("this case should not occur.")
      }

  // {Q[M<x <| e> / M]} *x := e; {Q}
  private fun replaceM(phi: AddressExpression, write: ArrayWrite): AddressExpression =
      when (phi) {
        is Variable -> phi
        is ArrayRead ->
            ArrayRead(replaceM(phi.array, write) as ArrayExpression, replaceM(phi.index, write))
        is ArrayWrite ->
            ArrayWrite(
                replaceM(phi.array, write) as ArrayExpression,
                replaceM(phi.index, write),
                replaceM(phi.value, write))
        is AnyArray -> ArrayWrite(write.array, write.index, write.value)
        // the other cases should not exist after prepare
        else -> throw Exception("this case is not supposed to be reachable: replaceM in $phi")
      }

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

  private fun replaceM(phi: ArithmeticExpression, write: ArrayWrite): ArithmeticExpression =
      when (phi) {
        is ValAtAddr -> ValAtAddr(replaceM(phi.addr, write))
        is NumericLiteral -> NumericLiteral(phi.literal)
        is UnaryMinus -> UnaryMinus(replaceM(phi.negated, write))
        is Add -> Add(replaceM(phi.left, write), replaceM(phi.right, write))
        is Sub -> Sub(replaceM(phi.left, write), replaceM(phi.right, write))
        is Mul -> Mul(replaceM(phi.left, write), replaceM(phi.right, write))
        is Div -> Div(replaceM(phi.left, write), replaceM(phi.right, write))
        is Rem -> Rem(replaceM(phi.left, write), replaceM(phi.right, write))
        is VarAddress -> throw Exception("expression ($phi) not supported by proof system.")
      }

  private fun prepare(phi: ArithmeticExpression): ArithmeticExpression =
      when (phi) {
        is ValAtAddr -> ValAtAddr(prepare(phi.addr))
        is NumericLiteral -> NumericLiteral(phi.literal)
        is UnaryMinus -> UnaryMinus(prepare(phi.negated))
        is Add -> Add(prepare(phi.left), prepare(phi.right))
        is Sub -> Sub(prepare(phi.left), prepare(phi.right))
        is Mul -> Mul(prepare(phi.left), prepare(phi.right))
        is Div -> Div(prepare(phi.left), prepare(phi.right))
        is Rem -> Rem(prepare(phi.left), prepare(phi.right))
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

  private fun replaceM(phi: BooleanExpression, write: ArrayWrite): BooleanExpression =
      when (phi) {
        is True -> phi
        is False -> phi
        is Not -> Not(replaceM(phi.negated, write))
        is Eq -> Eq(replaceM(phi.left, write), replaceM(phi.right, write), phi.nesting)
        is Gt -> Gt(replaceM(phi.left, write), replaceM(phi.right, write))
        is Gte -> Gte(replaceM(phi.left, write), replaceM(phi.right, write))
        is Lt -> Lt(replaceM(phi.left, write), replaceM(phi.right, write))
        is Lte -> Lte(replaceM(phi.left, write), replaceM(phi.right, write))
        is And -> And(replaceM(phi.left, write), replaceM(phi.right, write))
        is Equiv -> Equiv(replaceM(phi.left, write), replaceM(phi.right, write))
        is Imply -> Imply(replaceM(phi.left, write), replaceM(phi.right, write))
        is Or -> Or(replaceM(phi.left, write), replaceM(phi.right, write))
        // since bound vars are never program vars, we only need to replace on expression
        is Forall -> Forall(phi.boundVar, replaceM(phi.expression, write))
      }

  private fun prepare(phi: BooleanExpression): BooleanExpression {
    return when (phi) {
      is True -> phi
      is False -> phi
      is Not -> Not(prepare(phi.negated))
      is Eq -> Eq(prepare(phi.left), prepare(phi.right), phi.nesting)
      is Gt -> Gt(prepare(phi.left), prepare(phi.right))
      is Gte -> Gte(prepare(phi.left), prepare(phi.right))
      is Lt -> Lt(prepare(phi.left), prepare(phi.right))
      is Lte -> Lte(prepare(phi.left), prepare(phi.right))
      is And -> And(prepare(phi.left), prepare(phi.right))
      is Equiv -> Equiv(prepare(phi.left), prepare(phi.right))
      is Imply -> Imply(prepare(phi.left), prepare(phi.right))
      is Or -> Or(prepare(phi.left), prepare(phi.right))
      // since bound vars are never program vars, we only need to replace on expression
      is Forall -> Forall(phi.boundVar, prepare(phi.expression))
    }
  }

  fun augment(pre: BooleanExpression, scope: Scope): BooleanExpression {
    var newPre = prepare(pre)
    var addr = 0L
    for (entry in scope.symbols) {
      val value = if (entry.value.size == 1) 0 else addr + 1
      newPre =
          And(
              newPre,
              And(
                  Eq(
                      ValAtAddr(Variable(entry.key)),
                      ValAtAddr(ArrayRead(AnyArray, NumericLiteral(addr.toBigInteger()))),
                      0),
                  Eq(
                      ValAtAddr(ArrayRead(AnyArray, NumericLiteral(addr.toBigInteger()))),
                      NumericLiteral(value.toBigInteger()),
                      0)))
      addr++
      if (entry.value.size > 1) {
        for (i in 0 ..< entry.value.size - 1) {
          newPre =
              And(
                  newPre,
                  Eq(
                      ValAtAddr(ArrayRead(AnyArray, NumericLiteral(addr.toBigInteger()))),
                      NumericLiteral(BigInteger.ZERO),
                      0))
          addr++
        }
      }
    }
    return newPre
  }

  fun proof(): Boolean { // For backwards compatibility
    return check() is VerificationResult.Proof
  }

  override fun check(): VerificationResult {
    val pre = augment(context.pre, context.scope)
    val (_, vcs) = vcgen(pre, context.program, prepare(context.post))
    out.println("==== generating verification conditions: ====")
    var success = true
    vcs.forEach { out.println("$it") }
    for (vc in vcs) {
      out.println("---------------------------------------------")
      out.println("${vc.explanation}:")
      val expr = vc.smtTest()
      out.println("SMT Test: $expr")
      val solver = SMTSolver()
      val result = solver.solve(vc.smtTest())
      success = success and (result.status == SatStatus.UNSAT)
      out.println(
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
    out.println("=============================================")
    out.println("The proof was ${if (success) "" else "not "}successful.")
    return when (success) {
      true -> VerificationResult.Proof("All verification conditions were successfully proven.")
      false ->
          VerificationResult.Counterexample(
              "At least one verification condition could not be proven.")
    }
  }
}
