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

package tools.aqua.wvm.analysis.bmc

import tools.aqua.konstraints.util.reduceOrDefault
import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Context

class TransitionSystem(val context: Context, val verbose: Boolean = false) {
  // Possible system states s\in S_{V,\mu}
  val vars: List<String> = context.scope.symbols.map { it.key } // V //Also: loc
  var initial: BooleanExpression = True // all vars are zero // I
  var transitions: BooleanExpression = True // transition relation //\Gamma
  var invariant: BooleanExpression = True

  data class LocationID(var id: Int)

  val locId = LocationID(0)

  init {
    if (verbose) println("Variables: $vars")
    // Initial condition: All variables are zero and the location is 0 TODO: And precondition??
    initial = Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id).toBigInteger()), 0)
    for (entry in vars) {
      val varIsZero = Eq(ValAtAddr(Variable(entry)), NumericLiteral(0.toBigInteger()), 0)
      initial = And(initial, varIsZero)
    }
    if (verbose) println("Initial condition: $initial")

    // Transition relation
    transitions = context.program.asTransition(locId)
    if (verbose) println("Transition relation: $transitions")

    // Invariant: Either not at the end or the postcondition holds
    // TODO: Maybe change this to have a property that is checked every step as well (with a flag)
    val atEnd = Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id).toBigInteger()), 0)
    invariant = Or(Not(atEnd), context.post)
    if (verbose) println("Invariant: $invariant")
  }

  private fun List<Statement>.asTransition(locId: LocationID): BooleanExpression {
    return this.map { it.asTransition(locId) }.reduceOrDefault(True) { acc, next -> Or(acc, next) }
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
        And(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
            And(
                Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
                And(
                    this.cond,
                    vars
                        .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                        .reduceOrDefault(True) { acc, next -> And(acc, next) })))
    var thenBody = this.thenBlock.asTransition(locId)
    val lastIdThenBody = locId.id
    val ifFalseTransition =
        And(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((startId).toBigInteger()), 0),
            And(
                Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
                And(
                    Not(this.cond),
                    vars
                        .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                        .reduceOrDefault(True) { acc, next -> And(acc, next) })))
    val elseBody = this.elseBlock.asTransition(locId)
    // Changing last location id from the when-branch (currently in locId) to the last location
    // id from the else-branch
    thenBody = thenBody.changeLocation(lastIdThenBody, locId.id)
    return Or(Or(ifTrueTransition, thenBody), Or(ifFalseTransition, elseBody))
  }

  private fun While.asTransition(locId: LocationID): BooleanExpression {
    val startId = locId.id
    val whileTrueTransition =
        And(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
            And(
                Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
                And(
                    this.head,
                    vars
                        .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                        .reduceOrDefault(True) { acc, next -> And(acc, next) })))
    val loopBody = this.body.asTransition(locId).changeLocation(locId.id, startId)
    val whileFalseTransition =
        And(
            Eq(ValAtAddr(Variable("loc")), NumericLiteral(startId.toBigInteger()), 0),
            And(
                Eq(ValAtAddr(Variable("loc'")), NumericLiteral(locId.id.toBigInteger()), 0),
                And(
                    Not(this.head),
                    vars
                        .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                        .reduceOrDefault(True) { acc, next -> And(acc, next) })))
    return Or(whileTrueTransition, Or(loopBody, whileFalseTransition))
  }

  private fun Assignment.asTransition(locId: LocationID): BooleanExpression {
    return And(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        And(
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            if (vars.size > 1) {
              And(
                  Eq(this.expr, ValAtAddr(Variable("${this.addr}'")), 0),
                  vars
                      .filter { it != this.addr.toString() }
                      .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                      .reduceOrDefault(True) { acc, next -> And(acc, next) })
            } else {
              Eq(this.expr, ValAtAddr(Variable("${this.addr}'")), 0)
            }))
  }

  private fun Swap.asTransition(locId: LocationID): BooleanExpression {
    return And(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        And(
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            And(
                Eq(ValAtAddr(Variable("${this.left}'")), ValAtAddr(Variable("${this.right}")), 0),
                if (vars.size > 2) {
                  And(
                      Eq(
                          ValAtAddr(Variable("${this.right}'")),
                          ValAtAddr(Variable("${this.left}")),
                          0),
                      vars
                          .filter { it != this.left.toString() && it != this.right.toString() }
                          .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                          .reduceOrDefault(True) { acc, next -> And(acc, next) })
                } else {
                  Eq(ValAtAddr(Variable("${this.right}'")), ValAtAddr(Variable("${this.left}")), 0)
                })))
  }

  private fun Assertion.asTransition(locId: LocationID): BooleanExpression {
    return And(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        And(
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            And(
                this.cond,
                vars
                    .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                    .reduceOrDefault(True) { acc, next -> And(acc, next) })))
  }

  private fun Print.asTransition(locId: LocationID): BooleanExpression {
    return And(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        And(
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            vars
                .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) }))
  }

  private fun Havoc.asTransition(locId: LocationID): BooleanExpression {
    return And(
        Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
        And(
            Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
            And(
                Lte(NumericLiteral(this.lower), ValAtAddr(Variable("${this.addr}'"))),
                And(
                    Lt(ValAtAddr(Variable("${this.addr}'")), NumericLiteral(this.upper)),
                    vars
                        .filter { it != this.addr.toString() }
                        .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                        .reduceOrDefault(True) { acc, next -> And(acc, next) }))))
  }

  private fun Fail.asTransition(locId: LocationID): BooleanExpression {
    return False // TODO: Is this correct? Should it be a transition at all?
  }

  // Utils

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

  fun numberedTransitions(from: Int, to: Int): BooleanExpression {
    return transitions.renameVariables(
        vars.plus("loc").associateWith { "${it}$from" } +
            vars.plus("loc").map { "${it}'" }.associateWith { "${it.removeSuffix("'")}$to" })
  }

  fun zeroedInitial(): BooleanExpression {
    return initial.renameVariables(vars.plus("loc").associateWith { "${it}0" })
  }

  fun numberedInvariant(loc: Int): BooleanExpression {
    return invariant.renameVariables(vars.plus("loc").associateWith { "${it}$loc" })
  }
}
