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
  private val intSort: IntSort = SMTInt
  private val memSort = SMTArray(intSort, intSort)

  class Result(val status: SatStatus, val model: Map<String, String>)

  var vars = mapOf<String, DeclareConst<*>>()

  init {
    vars += (memArray to declareConst(memArray, memSort))
  }

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
    var commands = listOf<Command>(SetLogic(AUFLIA)) + vars.values + Assert(konstraint) + CheckSat
    val smtProgram = DefaultSMTProgram(commands)
    var model = emptyMap<String, String>()
    val status =
        Z3Solver().let { solver ->
          try {
            numberOfSolveCalls++
            solver.solve(smtProgram)
          } finally {
            solver.close()
          }
        }
    if (status == SatStatus.SAT) {
      try {
        commands += GetModel
        val progForModel = DefaultSMTProgram(commands)
        val solverModel =
            Z3Solver().let { solver ->
              try {
                numberOfSolveCalls++
                solver.solve(progForModel)
                solver.getModel()
              } finally {
                solver.close()
              }
            }
        model =
            solverModel.definitions
                .map { (key, value) -> key.toString() to value.term.toString() }
                .toMap()
      } catch (e: Exception) {
        // todo: produce some output
        // ex.printStackTrace()
        println("Error: ${e.message}")
      }
    }
    return Result(status, model)
  }
}
