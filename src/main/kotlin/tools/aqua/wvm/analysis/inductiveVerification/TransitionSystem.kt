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

package tools.aqua.wvm.analysis.inductiveVerification

import tools.aqua.konstraints.util.reduceOrDefault
import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Context

class TransitionSystem(
    val context: Context,
    val verbose: Boolean = false,
    val useWhileInvariant: Boolean = true
) {
  // Possible system states s\in S_{V,\mu}
  val vars: List<String> = context.scope.symbols.map { it.key } // V //Also: loc

  var initial: BooleanExpression = True // all vars are zero // I
  var transitions: BooleanExpression = True // transition relation //\Gamma
  var invariant: BooleanExpression = True

  data class LocationID(var id: Int)

  val locId = LocationID(0)

  init {
    if (verbose) println("Variables: $vars")
    // Initial condition: All variables are zero and the location is 0 and precondition holds
    var memIndex = 0
    val memInit =
        context.scope.symbols
            .map {
              when {
                it.value.type == BasicType.INT ->
                    listOf( // integer variable initialized to 0
                            Eq(
                                ValAtAddr(Variable(it.key)),
                                NumericLiteral(memIndex.toBigInteger()),
                                0),
                            Eq(
                                ValAtAddr(
                                    ArrayRead(
                                        AnyArray, NumericLiteral((memIndex++).toBigInteger()))),
                                NumericLiteral(0.toBigInteger()),
                                0))
                        .reduceOrDefault(True) { acc, next -> And(acc, next) }
                it.value.type is Pointer && it.value.size == 1 ->
                    listOf( // pointer to integer initialized to 0
                            Eq(
                                ValAtAddr(Variable(it.key)),
                                NumericLiteral(memIndex.toBigInteger()),
                                0),
                            Eq(
                                ValAtAddr(
                                    ArrayRead(
                                        AnyArray, NumericLiteral((memIndex++).toBigInteger()))),
                                NumericLiteral(0.toBigInteger()),
                                0))
                        .reduceOrDefault(True) { acc, next -> And(acc, next) }
                it.value.size > 1 ->
                    listOf( // array initialized to 0
                            Eq(
                                ValAtAddr(Variable(it.key)),
                                NumericLiteral(memIndex.toBigInteger()),
                                0),
                            Eq(
                                ValAtAddr(
                                    ArrayRead(AnyArray, NumericLiteral((memIndex).toBigInteger()))),
                                NumericLiteral(((memIndex++) + 1).toBigInteger()),
                                0),
                            (0 until it.value.size - 1)
                                .map {
                                  Eq(
                                      ValAtAddr(
                                          ArrayRead(
                                              AnyArray,
                                              NumericLiteral((memIndex++).toBigInteger()))),
                                      NumericLiteral(0.toBigInteger()),
                                      0)
                                }
                                .reduceOrDefault(True) { acc, next -> And(acc, next) })
                        .reduceOrDefault(True) { acc, next -> And(acc, next) }
                else ->
                    throw Exception(
                        "Unsupported variable type in transition system initial condition.")
              }
            }
            .reduceOrDefault(True) { acc, next -> And(acc, next) }

    val newPre = And(prepare(context.pre), memInit)
    val initialLoc = Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id).toBigInteger()), 0)
    // for (entry in vars) {
    //   val varIsZero = Eq(ValAtAddr(Variable(entry)), NumericLiteral(0.toBigInteger()), 0)
    //   initial = And(initial, varIsZero)
    // }
    initial = And(initialLoc, newPre)
    if (verbose) println("Initial condition: $initial")

    // Transition relation
    transitions = context.program.asTransition(locId)
    if (verbose) println("Transition relation: $transitions")

    // Invariant: (Not at error location) and (Either not at the end or the postcondition holds)
    // TODO: Maybe change this to have a property that is checked every step as well (with a flag)
    val atEnd = Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id).toBigInteger()), 0)
    // As a convention, error locations are labeled with negative numbers, more precisely in this
    // implementation there is only one error location, labeled "-1"
    val notError = Not(Lt(ValAtAddr(Variable("loc")), NumericLiteral(0.toBigInteger())))
    invariant = And(notError, Or(Not(atEnd), prepare(context.post)))
    if (verbose) println("Invariant: $invariant")
  }

  private fun prepare(phi: AddressExpression): AddressExpression =
      when (phi) {
        is Variable -> ArrayRead(AnyArray, ValAtAddr(phi))
        is DeRef -> ArrayRead(AnyArray, ValAtAddr(prepare(phi.reference)))
        is ArrayAccess -> ArrayRead(AnyArray, Add(prepare(phi.array), prepare(phi.index)))
        else -> throw Exception("this case should not occur. $phi")
      // is ArrayWrite -> ValAtAddr(ArrayWrite(phi.array, replace(phi.index, v, replacement),
      // replace(phi.value, v, replacement)))
      // is AnyArray -> throw Exception("this case should not occur.")
      }

  private fun prepare(expr: ArithmeticExpression): ArithmeticExpression =
      when (expr) {
        is ValAtAddr -> ValAtAddr(prepare(expr.addr))
        is NumericLiteral -> NumericLiteral(expr.literal)
        is UnaryMinus -> UnaryMinus(prepare(expr.negated))
        is Add -> Add(prepare(expr.left), prepare(expr.right))
        is Sub -> Sub(prepare(expr.left), prepare(expr.right))
        is Mul -> Mul(prepare(expr.left), prepare(expr.right))
        is Div -> Div(prepare(expr.left), prepare(expr.right))
        is Rem -> Rem(prepare(expr.left), prepare(expr.right))
        is VarAddress -> throw Exception("expression ($expr) not supported by proof system.")
      }

  private fun prepare(expr: BooleanExpression): BooleanExpression =
      when (expr) {
        is True -> expr
        is False -> expr
        is Not -> Not(prepare(expr.negated))
        is Eq -> Eq(prepare(expr.left), prepare(expr.right), expr.nesting)
        is Gt -> Gt(prepare(expr.left), prepare(expr.right))
        is Gte -> Gte(prepare(expr.left), prepare(expr.right))
        is Lt -> Lt(prepare(expr.left), prepare(expr.right))
        is Lte -> Lte(prepare(expr.left), prepare(expr.right))
        is And -> And(prepare(expr.left), prepare(expr.right))
        is Equiv -> Equiv(prepare(expr.left), prepare(expr.right))
        is Imply -> Imply(prepare(expr.left), prepare(expr.right))
        is Or -> Or(prepare(expr.left), prepare(expr.right))
        // since bound vars are never program vars, we only need to replace on expression
        is Forall -> Forall(expr.boundVar, prepare(expr.expression))
      }

  private fun List<Statement>.asTransition(locId: LocationID): BooleanExpression {
    return this.map { it.asTransition(locId) }.reduceOrDefault(False) { acc, next -> Or(acc, next) }
  }

  private fun SequenceOfStatements.asTransition(locId: LocationID): BooleanExpression {
    return this.statements.asTransition(locId)
  }

  private fun Statement.asTransition(locId: LocationID): BooleanExpression {
    return when (this) {
      is IfThenElse -> this.asTransition(locId)
      is While -> this.asTransition(locId)
      is Assertion -> this.asTransition(locId)
      is Assignment -> this.asTransition(locId)
      is Fail -> this.asTransition(locId)
      is Havoc -> this.asTransition(locId)
      is Print -> this.asTransition(locId)
      is Swap -> this.asTransition(locId)
    }
  }

  private fun IfThenElse.asTransition(locId: LocationID): BooleanExpression {
    val startId = locId.id
    val ifTrueTransition =
        makeSingleTransition(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            prepare(this.cond),
            vars
                .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) })
    var thenBody = this.thenBlock.asTransition(locId)
    val lastIdThenBody = locId.id
    val ifFalseTransition =
        makeSingleTransition(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((startId).toBigInteger()), 0),
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            Not(prepare(this.cond)),
            vars
                .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) })
    val elseBody = this.elseBlock.asTransition(locId)
    // Changing last location id from the when-branch (currently in locId) to the last location-id
    // from the else-branch
    thenBody = thenBody.changeLocation(lastIdThenBody, locId.id)
    return combineMultipleTransitions(ifTrueTransition, thenBody, ifFalseTransition, elseBody)
  }

  private fun While.asTransition(locId: LocationID): BooleanExpression {
    val startId = locId.id
    val whileTrueTransition =
        makeSingleTransition(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            prepare(this.head), // boolean condition
            vars
                .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) },
            if (useWhileInvariant) this.invariant else True)
    val loopBody = this.body.asTransition(locId).changeLocation(locId.id, startId)
    val whileFalseTransition =
        makeSingleTransition(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral(startId.toBigInteger()), 0),
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral(locId.id.toBigInteger()), 0),
            Not(prepare(this.head)),
            vars
                .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) },
            if (useWhileInvariant) this.invariant else True)
    return combineMultipleTransitions(whileTrueTransition, loopBody, whileFalseTransition)
  }

  private fun Assignment.asTransition(locId: LocationID): BooleanExpression {
    return makeSingleTransition(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
        when (this.addr) {
          is Variable ->
              Eq(
                  ValAtAddr(AnyArrayPrimed),
                  ValAtAddr(ArrayWrite(AnyArray, ValAtAddr(this.addr), prepare(this.expr))),
                  0)
          is DeRef ->
              Eq(
                  ValAtAddr(AnyArrayPrimed),
                  ValAtAddr(
                      ArrayWrite(
                          AnyArray,
                          ValAtAddr(ArrayRead(AnyArray, ValAtAddr(this.addr.reference))),
                          prepare(this.expr))),
                  0,
              )
          is ArrayAccess ->
              Eq(
                  ValAtAddr(AnyArrayPrimed),
                  ValAtAddr(
                      ArrayWrite(
                          AnyArray,
                          Add(
                              ValAtAddr(ArrayRead(AnyArray, this.addr.array)),
                              prepare(this.addr.index)),
                          prepare(this.expr))),
                  0,
              )
          else ->
              throw Exception(
                  "Assignment to non-variable addresses is not supported in the transition system.")
        },
        vars
            .filter { it != this.addr.toString() }
            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
            .reduceOrDefault(True) { acc, next -> And(acc, next) })
  }

  private fun Swap.asTransition(locId: LocationID): BooleanExpression {
    return makeSingleTransition(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
        Eq(ValAtAddr(Variable("${this.left}'")), ValAtAddr(Variable("${this.right}")), 0),
        Eq(ValAtAddr(Variable("${this.right}'")), ValAtAddr(Variable("${this.left}")), 0),
        vars
            .filter { it != this.left.toString() && it != this.right.toString() }
            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
            .reduceOrDefault(True) { acc, next -> And(acc, next) })
  }

  private fun Assertion.asTransition(locId: LocationID): BooleanExpression {
    val startId = locId.id
    return combineMultipleTransitions(
        makeSingleTransition( // Assertion holds
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            prepare(this.cond),
            vars
                .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) }),
        makeSingleTransition( // Assertion violated, -1 indicates the error location
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((startId).toBigInteger()), 0),
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((-1).toBigInteger()), 0),
            Not(this.cond),
            vars
                .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) }))
  }

  private fun Print.asTransition(locId: LocationID): BooleanExpression {
    return makeSingleTransition(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
        vars
            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
            .reduceOrDefault(True) { acc, next -> And(acc, next) })
  }

  private fun Havoc.asTransition(locId: LocationID): BooleanExpression {
    return makeSingleTransition(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
        Lte(NumericLiteral(this.lower), ValAtAddr(Variable("${this.addr}'"))),
        Lt(ValAtAddr(Variable("${this.addr}'")), NumericLiteral(this.upper)),
        vars
            .filter { it != this.addr.toString() }
            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
            .reduceOrDefault(True) { acc, next -> And(acc, next) })
  }

  private fun Fail.asTransition(locId: LocationID): BooleanExpression {
    return makeSingleTransition( // -1 indicates the error location
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        Eq(ValAtAddr(Variable("loc'")), NumericLiteral((-1).toBigInteger()), 0),
        vars
            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
            .reduceOrDefault(True) { acc, next -> And(acc, next) })
  }

  // Utils

  private fun makeSingleTransition(vararg elements: BooleanExpression) =
      listOf(*elements).filter { it !is True }.reduceOrDefault(True) { acc, next -> And(acc, next) }

  private fun combineMultipleTransitions(vararg elements: BooleanExpression) =
      listOf(*elements).filter { it !is True }.reduceOrDefault(False) { acc, next -> Or(acc, next) }

  private fun BooleanExpression.changeLocation(currentId: Int, newId: Int): BooleanExpression {
    return when (this) {
      is Eq -> {
        if (this.left is ValAtAddr &&
            ((this.left.addr as Variable).name == "loc" || this.left.addr.name == "loc'") &&
            this.right is NumericLiteral &&
            this.right.literal == currentId.toBigInteger()) {
          Eq(ValAtAddr(Variable(this.left.addr.name)), NumericLiteral(newId.toBigInteger()), 0)
        } else {
          this
        }
      }
      is And -> And(left.changeLocation(currentId, newId), right.changeLocation(currentId, newId))
      is Or -> Or(left.changeLocation(currentId, newId), right.changeLocation(currentId, newId))
      is Not -> Not(negated.changeLocation(currentId, newId))
      else -> this // Other expressions are not handled here TODO: Are more necessary?
    }
  }

  // Temporal transition system expressions

  fun numberedTransitions(from: Int, to: Int): BooleanExpression {
    return transitions.renameVariables(
        vars.plus("loc").plus("M").associateWith { "${it}$from" } +
            vars
                .plus("loc")
                .plus("M")
                .map { "${it}'" }
                .associateWith { "${it.removeSuffix("'")}$to" })
  }

  fun zeroedInitial(): BooleanExpression {
    return initial.renameVariables(vars.plus("loc").plus("M").associateWith { "${it}0" })
  }

  fun numberedInvariant(loc: Int): BooleanExpression {
    return invariant.renameVariables(vars.plus("loc").plus("M").associateWith { "${it}$loc" })
  }
}
