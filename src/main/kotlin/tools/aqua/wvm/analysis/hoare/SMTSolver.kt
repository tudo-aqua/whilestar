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

import tools.aqua.konstraints.parser.Context
import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.solvers.z3.Z3Solver
import tools.aqua.konstraints.theories.*
import tools.aqua.konstraints.util.reduceOrDefault
import tools.aqua.wvm.language.*
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.False
import tools.aqua.wvm.language.Not
import tools.aqua.wvm.language.Or
import tools.aqua.wvm.language.True

class SMTSolver(val booleanEvaluation: Boolean = false, val wpcMode: Boolean = true) {

  val memArray = "M_"

  class Result(val status: SatStatus, val model: Map<String, String>)

  var vars = mapOf<String, DeclareConst>()

  val ctx = Context(AUFLIA)

  val seenModels = mutableListOf<Map<String, String>>()

  init {
    vars += (memArray to DeclareConst(Symbol(memArray), ArraySort(IntSort, IntSort)))
  }

  companion object {
    var numberOfSolveCalls = 0
    var numberOfSimplifyCalls = 0
    var NumberOfInterpolantCalls = 0
    val numberOfSMTCalls
      get() = numberOfSolveCalls + numberOfSimplifyCalls + NumberOfInterpolantCalls

    fun resetCallCounters() {
      numberOfSolveCalls = 0
      numberOfSimplifyCalls = 0
      NumberOfInterpolantCalls = 0
    }
  }

  fun asKonstraint(expr: ArrayExpression): Expression<*> =
      when (expr) {
        is AnyArray -> UserDeclaredExpression(Symbol(memArray), ArraySort(IntSort, IntSort))
        is NamedArray if !this.wpcMode-> {
            if (!vars.containsKey(expr.name)) {
              vars +=
                  (expr.name to DeclareConst(Symbol(expr.name), ArraySort(IntSort, IntSort)))
            }
            UserDeclaredExpression(Symbol(expr.name), ArraySort(IntSort, IntSort))
        }
        is ArrayRead ->
            ArraySelect(asKonstraint(expr.array) as Expression<ArraySort>, asKonstraint(expr.index))
                as Expression<IntSort>
        is ArrayWrite ->
            ArrayStore(
                asKonstraint(expr.array) as Expression<ArraySort>,
                asKonstraint(expr.index),
                asKonstraint(expr.value))
        else -> throw Exception("oh no")
      }

  fun asKonstraint(expr: AddressExpression): Expression<IntSort> {
    if (expr is Variable) {
      if (!vars.containsKey(expr.name)) {
        vars += (expr.name to DeclareConst(Symbol(expr.name), IntSort))
      }
      return UserDeclaredExpression(Symbol(expr.name), IntSort)
    } else if (expr is ArrayRead) {
      return asKonstraint(expr) as Expression<IntSort>
    } else if (!this.wpcMode && expr is ArrayWrite) {
      return asKonstraint(expr) as Expression<IntSort>
    } else if (!this.wpcMode && expr is NamedArray) {
      if (!vars.containsKey(expr.name)) {
        vars += (expr.name to DeclareConst(Symbol(expr.name), ArraySort(IntSort, IntSort)))
      }
      return UserDeclaredExpression(Symbol(expr.name), ArraySort(IntSort, IntSort)) as Expression<IntSort>
    } else if (!this.wpcMode) {
        throw Exception("SMT Solver cannot compute with address expression ${expr}")
    } else throw Exception("WPC Proof System cannot compute with address expression ${expr}")
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
        is Div -> IntDiv(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is Mul -> IntMul(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is Rem -> Mod(asKonstraint(expr.left), asKonstraint(expr.right))
        is Sub -> IntSub(listOf(asKonstraint(expr.left), asKonstraint(expr.right)))
        is UnaryMinus -> IntNeg(asKonstraint(expr.negated))
        is ValAtAddr -> asKonstraint(expr.addr)
        is VarAddress -> throw Exception("WPC Proof System cannot compute with var address ${expr}")
      // is ArrayRead -> ArraySelect(asKonstraint(expr.array), asKonstraint(expr.index)) as
      // Expression<IntSort>
      }

  fun asKonstraint(expr: BooleanExpression): Expression<BoolSort> =
      when (expr) {
        is True -> tools.aqua.konstraints.theories.True
        is False -> tools.aqua.konstraints.theories.False
        is And ->
            tools.aqua.konstraints.theories.And(asKonstraint(expr.left), asKonstraint(expr.right))
        is Or ->
            tools.aqua.konstraints.theories.Or(asKonstraint(expr.left), asKonstraint(expr.right))
        is Imply -> Implies(asKonstraint(expr.left), asKonstraint(expr.right))
        is Equiv -> Equals(asKonstraint(expr.left), asKonstraint(expr.right))
        is Not -> tools.aqua.konstraints.theories.Not(asKonstraint(expr.negated))
        is Gt -> IntGreater(asKonstraint(expr.left), asKonstraint(expr.right))
        is Gte -> IntGreaterEq(asKonstraint(expr.left), asKonstraint(expr.right))
        is Lt -> IntLess(asKonstraint(expr.left), asKonstraint(expr.right))
        is Lte -> IntLessEq(asKonstraint(expr.left), asKonstraint(expr.right))
        is Eq -> Equals(asKonstraint(expr.left), asKonstraint(expr.right))
        is Forall ->
            ForallExpression(
                listOf(SortedVar(Symbol(expr.boundVar.name), IntSort)),
                asKonstraint(expr.expression))
      }

  fun asExpression(expr: Expression<*>): tools.aqua.wvm.language.Expression<*> =
      when (expr) {
        is UserDeclaredExpression ->
            if (expr.sort == ArraySort(IntSort, IntSort)) {
              AnyArray
            } else if (expr.sort == IntSort) {
              ValAtAddr(Variable(expr.name.value))
            } else {
              throw Exception("Unkown UserDeclaredExpression $expr")
            }
        is ArraySelect ->
            ArrayRead(
                asExpression(expr.array) as ArrayExpression,
                asExpression(expr.index) as ArithmeticExpression)
        is ArrayStore ->
            ArrayWrite(
                asExpression(expr.array) as ArrayExpression,
                asExpression(expr.index) as ArithmeticExpression,
                asExpression(expr.value) as ArithmeticExpression)
        is IntLiteral -> NumericLiteral(expr.value)
        is IntAdd ->
            Add(
                asExpression(expr.terms[0]) as ArithmeticExpression,
                asExpression(expr.terms[1]) as ArithmeticExpression)
        is IntDiv ->
            Div(
                asExpression(expr.terms[0]) as ArithmeticExpression,
                asExpression(expr.terms[1]) as ArithmeticExpression)
        is IntMul ->
            Mul(
                asExpression(expr.factors[0]) as ArithmeticExpression,
                asExpression(expr.factors[1]) as ArithmeticExpression)
        is Mod ->
            Rem(
                asExpression(expr.dividend) as ArithmeticExpression,
                asExpression(expr.divisor) as ArithmeticExpression)
        is IntSub ->
            Sub(
                asExpression(expr.terms[0]) as ArithmeticExpression,
                asExpression(expr.terms[1]) as ArithmeticExpression)
        is IntNeg -> UnaryMinus(asExpression(expr.inner) as ArithmeticExpression)
        is tools.aqua.konstraints.theories.True -> True
        is tools.aqua.konstraints.theories.False -> False
        is tools.aqua.konstraints.theories.And ->
            expr.conjuncts
                .map { asExpression(it) as BooleanExpression }
                .reduce { exp1, exp2 -> And(exp1, exp2) }
        is tools.aqua.konstraints.theories.Or ->
            expr.disjuncts
                .map { asExpression(it) as BooleanExpression }
                .reduce { exp1, exp2 -> Or(exp1, exp2) }
        is Implies ->
            Imply(
                asExpression(expr.children[0]) as BooleanExpression,
                asExpression(expr.children[1]) as BooleanExpression)
        is tools.aqua.konstraints.theories.Not -> Not(asExpression(expr.inner) as BooleanExpression)
        is IntGreater ->
            Gt(
                asExpression(expr.terms[0]) as ArithmeticExpression,
                asExpression(expr.terms[1]) as ArithmeticExpression)
        is IntGreaterEq ->
            Gte(
                asExpression(expr.terms[0]) as ArithmeticExpression,
                asExpression(expr.terms[1]) as ArithmeticExpression)
        is IntLess ->
            Lt(
                asExpression(expr.terms[0]) as ArithmeticExpression,
                asExpression(expr.terms[1]) as ArithmeticExpression)
        is IntLessEq ->
            Lte(
                asExpression(expr.terms[0]) as ArithmeticExpression,
                asExpression(expr.terms[1]) as ArithmeticExpression)
        is Equals ->
            Eq(
                asExpression(expr.children[0]) as ArithmeticExpression,
                asExpression(expr.children[1]) as ArithmeticExpression,
                0)
        is Equals -> // TODO: distinguish between equals and equivalence in the SMT output
        Equiv(
                asExpression(expr.children[0]) as BooleanExpression,
                asExpression(expr.children[1]) as BooleanExpression)
        is ForallExpression ->
            Forall(Variable(expr.vars[0].name.value), asExpression(expr.term) as BooleanExpression)
        else -> throw Exception("oh no")
      }

  fun solve(expr: BooleanExpression): Result {
    val konstraint = asKonstraint(expr)
    return solve(konstraint)
  }

  fun solve(expr: Expression<BoolSort>): Result {
    val oldModels =
        seenModels
            .map {
              it.entries
                  .map {
                    Eq(ValAtAddr(Variable(it.key)), NumericLiteral(it.value.toBigInteger()), 0)
                  }
                  .reduce<BooleanExpression, Eq> { acc, eq -> And(acc, eq) }
            }
            .reduceOrDefault(False) { exp1, exp2 -> Or(exp1, exp2) }
    val konstraint = tools.aqua.konstraints.theories.And(expr, asKonstraint(Not(oldModels)))
    val commands = (vars.values + Assert(konstraint)).toMutableList()
    if (booleanEvaluation) {
      // Add to konstraint that all variables but the memory and "loc" are boolean, i.e. equal to 0
      // or 1
      val booleanVars =
          vars.keys
              .filter { it != "M_" && it != "loc" }
              .map {
                Or(
                    Eq(ValAtAddr(Variable(it)), NumericLiteral(0.toBigInteger()), 0),
                    Eq(ValAtAddr(Variable(it)), NumericLiteral(1.toBigInteger()), 0))
              }
              .reduceOrDefault(True) { acc, next -> And(acc, next) }
      val locConstraint =
          vars.keys
              .filter { it == "loc" } // Only if loc is present
              .map { Gte(ValAtAddr(Variable(it)), NumericLiteral(0.toBigInteger())) }
              .reduceOrDefault(True) { acc, next -> And(acc, next) }
      val booleanVarsKonstraint = asKonstraint(And(booleanVars, locConstraint))
      commands += Assert(booleanVarsKonstraint)
    }
    commands += CheckSat
    val smtProgram = DefaultSMTProgram(commands, ctx)
    var model = emptyMap<String, String>()
    smtProgram.solve().also { numberOfSolveCalls++ }
    if (smtProgram.status == SatStatus.SAT) {
      try {
        commands += GetModel
        val progForModel = DefaultSMTProgram(commands, ctx)
        progForModel.solve().also { numberOfSolveCalls++ }
        model =
            progForModel.model?.definitions?.associate { it ->
              (it.name.toString() to it.term.toString())
            } ?: emptyMap()
        seenModels.addLast(model)
        // println(model)
      } catch (ex: Exception) {
        // todo: produce some output
        println("oops.: $ex")
      }
    }
    return Result(smtProgram.status, model)
  }

  fun simplify(expr: BooleanExpression): BooleanExpression {
    val term = asKonstraint(expr)
    val termSimplified = simplify(term)

    return asExpression(termSimplified) as BooleanExpression
  }

  fun simplify(term: Expression<BoolSort>): Expression<BoolSort> {
    val z3 = Z3Solver()
    val termSimplified = z3.simplify(vars.values.toList(), term).also { numberOfSolveCalls++ }
    return termSimplified
  }

  /**
   * If possible, computes an interpolant for two boolean expressions exprA and exprB such that
   * exprA implies the interpolant and the interpolant is unsatisfiable with exprB. A => I and I & B
   * is unsat.
   */
  fun computeInterpolant(exprA: BooleanExpression, exprB: BooleanExpression): BooleanExpression? {
    if (booleanEvaluation) { // Boolean Variables: Does not work for every theory
      return computeBooleanTheoryInterpolant(exprA, exprB)
    }
    // Standard way: Use the interpolation feature of the Konstraints library
    val konstraintA = asKonstraint(exprA) // Also registers variables in vars
    val konstraintB = asKonstraint(exprB)
    val commands = vars.values + ComputeInterpolant(listOf(konstraintA, konstraintB))
    val smtProgram = InterpolatingSMTProgram(commands, ctx)
    smtProgram.solve().also { numberOfSolveCalls++ }
    val interpolants = smtProgram.interpolant?.interpolants
    return if (interpolants?.size == 1) asExpression(interpolants[0]) as BooleanExpression else null
  }

  fun computeBooleanTheoryInterpolant(
      exprA: BooleanExpression,
      exprB: BooleanExpression
  ): BooleanExpression? {
    // Usually exprB is the model looking like a == 1 & b == 0 & c == 1 ...
    // Use subsets of the model to find a smaller interpolant
    val modelParts = mutableListOf<BooleanExpression>()
    var m = exprB
    while (m is And) {
      modelParts.add(m.right)
      m = m.left
    }
    modelParts.add(m)
    // Generate power set of modelParts, each as a single BooleanExpression connected with And
    val powerSet =
        (1 until (1 shl modelParts.size)).map { mask ->
          val subset = modelParts.filterIndexed { idx, _ -> (mask and (1 shl idx)) != 0 }
          subset.reduce { acc, exp -> And(acc, exp) }
        }
    // Add to konstraint that all variables but the memory and "loc" are boolean, i.e. equal to 0 or
    // 1
    val booleanVars =
        vars.keys
            .filter { it != "M_" && it != "loc" }
            .map {
              Or(
                  Eq(ValAtAddr(Variable(it)), NumericLiteral(0.toBigInteger()), 0),
                  Eq(ValAtAddr(Variable(it)), NumericLiteral(1.toBigInteger()), 0))
            }
            .reduceOrDefault(True) { acc, next -> And(acc, next) }
    val booleanVarsKonstraint = asKonstraint(booleanVars)
    for (part in powerSet) {
      val konstraint = asKonstraint(exprA) // Also registers variables in vars
      val phi = asKonstraint(part)
      // M \models \phi by construction
      // Test a \models \not\phi
      val commands =
          vars.values + Assert(konstraint) + Assert(booleanVarsKonstraint) + Assert(phi) + CheckSat
      val smtProgram = DefaultSMTProgram(commands, ctx)
      smtProgram.solve().also { numberOfSolveCalls++ }
      if (smtProgram.status == SatStatus.UNSAT) {
        return Not(asExpression(phi) as BooleanExpression)
      }
    }
    return null
  }
}
