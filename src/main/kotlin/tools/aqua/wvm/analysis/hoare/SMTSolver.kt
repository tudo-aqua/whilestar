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
import tools.aqua.konstraints.dsl.UserDeclaredSMTFunction0
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.solvers.z3.Z3Solver
import tools.aqua.wvm.language.*
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.False
import tools.aqua.wvm.language.Not
import tools.aqua.wvm.language.Or
import tools.aqua.wvm.language.True
import tools.aqua.wvm.language.Variable

class SMTSolver {

  val memArray = "M_"
  private val solverTimeoutMs = 5_000L
  private val intSort: IntSort = SMTInt
  private val memSort = SMTArray(intSort, intSort)

  class Result(
      val status: SatStatus,
      val model: Map<String, String>,
      val modelAvailable: Boolean = true
  ) {
    fun modelText(): String =
        if (modelAvailable) model.toSortedMap().toString()
        else "(model not representable by konstraints)"
  }

  // the memory is declared on first use (see getArrayVar), so queries that do not mention it keep
  // a printable model instead of the constant array that konstraints cannot serialize
  var vars = mapOf<String, DeclareConst<*>>()

  companion object {
    var numberOfSolveCalls = 0
    val numberOfSMTCalls
      get() = numberOfSolveCalls

    fun resetCallCounters() {
      numberOfSolveCalls = 0
    }
  }

  @Suppress("UNCHECKED_CAST")
  private fun <T : Sort> declareConst(name: String, sort: T): DeclareConst<T> {
    val function = UserDeclaredSMTFunction0(Symbol(name), sort)
    return DeclareConst(function.instance)
  }

  @Suppress("UNCHECKED_CAST")
  private fun getIntVar(name: String): Expression<IntSort> {
    if (!vars.containsKey(name)) {
      vars += (name to declareConst(name, intSort))
    }
    return (vars[name] as DeclareConst<IntSort>).instance
  }

  @Suppress("UNCHECKED_CAST")
  private fun getArrayVar(name: String): Expression<ArraySort<IntSort, IntSort>> {
    if (!vars.containsKey(name)) {
      vars += (name to declareConst(name, memSort))
    }
    return (vars[name] as DeclareConst<ArraySort<IntSort, IntSort>>).instance
  }

  @Suppress("UNCHECKED_CAST")
  fun asKonstraint(expr: ArrayExpression): Expression<*> =
      when (expr) {
        is AnyArray -> getArrayVar(memArray)
        is NamedArray -> {
          getArrayVar(expr.name)
        }
        is ArrayRead ->
            ArraySelect(
                asKonstraint(expr.array) as Expression<ArraySort<IntSort, IntSort>>,
                asKonstraint(expr.index))
                as Expression<IntSort>
        is ArrayWrite ->
            ArrayStore(
                asKonstraint(expr.array) as Expression<ArraySort<IntSort, IntSort>>,
                asKonstraint(expr.index),
                asKonstraint(expr.value))
        else -> throw Exception("oh no")
      }

  @Suppress("UNCHECKED_CAST")
  fun asKonstraint(expr: AddressExpression): Expression<IntSort> {
    if (expr is Variable) {
      return getIntVar(expr.name)
    } else if (expr is ArrayRead) {
      return asKonstraint(expr) as Expression<IntSort>
    } else if (expr is ArrayWrite) {
      return asKonstraint(expr) as Expression<IntSort>
    } else if (expr is NamedArray) {
      return getArrayVar(expr.name) as Expression<IntSort>
    } else
        throw IllegalSymbolException(
            "WPC Proof System cannot compute with address expression ${expr}")
  }

  fun asKonstraint(expr: ArithmeticExpression): Expression<IntSort> =
      when (expr) {
        is NumericLiteral ->
            if (expr.literal < 0.toBigInteger()) {
              IntNeg(IntLiteral(-expr.literal))
            } else {
              IntLiteral(expr.literal)
            }
        is Add -> IntAdd(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is Div -> truncatingDiv(asKonstraint(expr.left), asKonstraint(expr.right))
        is Mul -> IntMul(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is Rem -> truncatingRem(asKonstraint(expr.left), asKonstraint(expr.right))
        is Sub -> IntSub(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is UnaryMinus -> IntNeg(asKonstraint(expr.negated))
        is ValAtAddr -> asKonstraint(expr.addr)
        is VarAddress -> asKonstraint(ValAtAddr(expr.variable))
      // is ArrayRead -> ArraySelect(asKonstraint(expr.array), asKonstraint(expr.index)) as
      // Expression<IntSort>
      }

  fun asKonstraint(expr: BooleanExpression): Expression<BoolSort> =
      when (expr) {
        is True -> tools.aqua.konstraints.smt.True
        is False -> tools.aqua.konstraints.smt.False
        is And -> tools.aqua.konstraints.smt.And(asKonstraint(expr.left), asKonstraint(expr.right))
        is Or -> tools.aqua.konstraints.smt.Or(asKonstraint(expr.left), asKonstraint(expr.right))
        is Imply -> Implies(asKonstraint(expr.left), asKonstraint(expr.right))
        is Equiv -> Equals(asKonstraint(expr.left), asKonstraint(expr.right))
        is Not -> tools.aqua.konstraints.smt.Not(asKonstraint(expr.negated))
        is Gt -> IntGreater(asKonstraint(expr.left), asKonstraint(expr.right))
        is Gte -> IntGreaterEq(asKonstraint(expr.left), asKonstraint(expr.right))
        is Lt -> IntLess(asKonstraint(expr.left), asKonstraint(expr.right))
        is Lte -> IntLessEq(asKonstraint(expr.left), asKonstraint(expr.right))
        is Eq -> Equals(asKonstraint(expr.left), asKonstraint(expr.right))
        is Forall ->
            ForallExpression(
                listOf(SortedVar(Symbol(expr.boundVar.name), intSort)),
                asKonstraint(expr.expression))
      }

  /**
   * SMT-LIB integer division is Euclidean (0 <= mod < |divisor|), whereas the interpreter truncates
   * towards zero (BigInteger.divide/rem). Both agree unless the dividend is negative and the
   * division is inexact; then the quotient is moved one step towards zero and the remainder becomes
   * negative.
   */
  private fun truncatingDiv(
      dividend: tools.aqua.konstraints.smt.Expression<IntSort>,
      divisor: tools.aqua.konstraints.smt.Expression<IntSort>
  ): tools.aqua.konstraints.smt.Expression<IntSort> {
    val quotient = IntDiv(listOf(dividend, divisor))
    val adjust = negativeDividendAndRemainder(dividend, divisor)
    return Ite(adjust, IntAdd(listOf(quotient, divisorSign(divisor))), quotient)
  }

  private fun truncatingRem(
      dividend: tools.aqua.konstraints.smt.Expression<IntSort>,
      divisor: tools.aqua.konstraints.smt.Expression<IntSort>
  ): tools.aqua.konstraints.smt.Expression<IntSort> {
    val remainder = Mod(dividend, divisor)
    val adjust = negativeDividendAndRemainder(dividend, divisor)
    return Ite(adjust, IntSub(listOf(remainder, absolute(divisor))), remainder)
  }

  private fun negativeDividendAndRemainder(
      dividend: tools.aqua.konstraints.smt.Expression<IntSort>,
      divisor: tools.aqua.konstraints.smt.Expression<IntSort>
  ): tools.aqua.konstraints.smt.Expression<BoolSort> {
    val zero = IntLiteral(BigInteger.ZERO)
    val dividendNegative = IntLess(listOf(dividend, zero))
    val remainder = tools.aqua.konstraints.smt.Not(Equals(Mod(dividend, divisor), zero))
    return tools.aqua.konstraints.smt.And(dividendNegative, remainder)
  }

  private fun divisorSign(
      divisor: tools.aqua.konstraints.smt.Expression<IntSort>
  ): tools.aqua.konstraints.smt.Expression<IntSort> {
    val zero = IntLiteral(BigInteger.ZERO)
    return Ite(
        IntGreater(listOf(divisor, zero)),
        IntLiteral(BigInteger.ONE),
        IntNeg(IntLiteral(BigInteger.ONE)))
  }

  private fun absolute(
      divisor: tools.aqua.konstraints.smt.Expression<IntSort>
  ): tools.aqua.konstraints.smt.Expression<IntSort> {
    val zero = IntLiteral(BigInteger.ZERO)
    return Ite(IntLess(listOf(divisor, zero)), IntNeg(divisor), divisor)
  }

  fun solve(expr: BooleanExpression): Result {
    val konstraint = asKonstraint(expr)
    val commands = listOf<Command>(SetLogic(AUFLIA)) + vars.values + Assert(konstraint)
    val smtProgram = DefaultSMTProgram(commands)
    return try {
      runSolver(smtProgram, produceModel = true)
    } catch (e: Exception) {
      // konstraints cannot convert every model Z3 returns: a constant array (the memory is one)
      // makes the declaration map reject the model and the whole proof would fail. The
      // satisfiability answer is already decided at that point, so ask once more without a model.
      val fallback = runSolver(smtProgram, produceModel = false)
      Result(fallback.status, emptyMap(), modelAvailable = false)
    }
  }

  private fun runSolver(smtProgram: SMTProgram, produceModel: Boolean): Result {
    // counted here so that the repeated query of solve's fallback shows up as well
    numberOfSolveCalls++
    val (status, solverModel) =
        Z3Solver().let { solver ->
          try {
            solver.solve(smtProgram, produceModel = produceModel, timeout = solverTimeoutMs)
          } finally {
            solver.close()
          }
        }
    val model =
        solverModel
            ?.definitions
            ?.map { (key, value) -> key.toString() to value.term.toString() }
            ?.toMap() ?: emptyMap()
    return Result(status, model)
  }
}
