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

  class Result(val status: SatStatus, val model: Map<String, String>)

  // The memory array constant [memArray] ("M_") is NOT declared
  // unconditionally. It is declared lazily in [getArrayVar] as soon as the
  // verification condition actually contains an array expression (e.g. an
  // [AnyArray] node). Declaring it unconditionally would crash the Z3 model
  // extraction for SAT (failed proof) results, since an unconstrained
  // constant has no interpretation in the produced model (konstraints-z3
  // NPE on getConstInterp).
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

  fun solve(expr: BooleanExpression): Result {
    val konstraint = asKonstraint(expr)
    val commands = listOf<Command>(SetLogic(AUFLIA)) + vars.values + Assert(konstraint)
    val smtProgram = DefaultSMTProgram(commands)
    val solver = Z3Solver()
    try {
      numberOfSolveCalls++
      val (status, solverModel) =
          solver.solve(smtProgram, produceModel = true, timeout = solverTimeoutMs)
      val model =
          solverModel
              ?.definitions
              ?.map { (key, value) -> key.toString() to value.term.toString() }
              ?.toMap() ?: emptyMap()
      return Result(status, model)
    } catch (e: Exception) {
      // Safety net: konstraints-z3 can crash while converting the Z3 model into an
      // aqua model even though solving itself succeeded (e.g. an NPE when a declared
      // constant such as [memArray] is unconstrained, or a RuntimeException when the
      // model represents an array as a constant array). Z3Solver sets its status right
      // after check() and only then starts model extraction, so a non-PENDING status
      // here means the solve result is valid and only the model extraction failed.
      // The model is only used for string display by the callers, so we fall back to
      // a best-effort model extracted directly from the raw Z3 API.
      if (solver.status == SatStatus.PENDING) {
        throw e
      }
      System.err.println(
          "WARNING: Z3 model extraction failed after solving (status ${solver.status}): " +
              "${e.javaClass.simpleName}: ${e.message}")
      return Result(solver.status, extractRawModel(solver))
    } finally {
      solver.close()
    }
  }

  /**
   * Best-effort model extraction using the raw Z3 API. Used as a fallback when the model conversion
   * of konstraints-z3 crashes. The values are rendered using Z3's own toString (SMT-LIB style),
   * which is sufficient for the string-only display use cases of the model.
   */
  private fun extractRawModel(solver: Z3Solver): Map<String, String> {
    return try {
      val rawModel = solver.solver.model ?: return emptyMap()
      rawModel.decls.associate { decl -> decl.name.toString() to rawModelValue(rawModel, decl) }
    } catch (e: Exception) {
      emptyMap()
    }
  }

  private fun rawModelValue(
      rawModel: com.microsoft.z3.Model,
      decl: com.microsoft.z3.FuncDecl<*>
  ): String {
    return try {
      when (decl.arity) {
        0 ->
            try {
              rawModel.getConstInterp(decl)?.toString()
            } catch (e: Exception) {
              rawModel.getFuncInterp(decl)?.toString()
            }
        else -> rawModel.getFuncInterp(decl)?.toString()
      } ?: "(no interpretation)"
    } catch (e: Exception) {
      "(no interpretation)"
    }
  }
}
