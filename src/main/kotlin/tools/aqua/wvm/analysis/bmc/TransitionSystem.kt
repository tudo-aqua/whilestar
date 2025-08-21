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
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Context

class TransitionSystem(val context: Context, val verbose: Boolean = false) {
  // Possible system states s\in S_{V,\mu}
  val vars: List<String> = context.scope.symbols.map { it.key } // V
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
    val initialKonstraint = SMTSolver().asKonstraint(initial)
    if (verbose) println("Initial as Konstraint: $initialKonstraint")

    // Transition relation
    transitions = transitionForStatements(context.program, locId)
    if (verbose) println("Transition relation: $transitions")
    // val transitionKonstraint = SMTSolver().asKonstraint(numberedTransitions(0, 1))
    // println("Transition relation as Konstraint: $transitionKonstraint")

    // Invariant: Either not at the end or the postcondition holds
    // TODO: Maybe change this to have a property that is checked every step as well (with a flag)
    invariant =
        Or(
            Not(Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id).toBigInteger()), 0)),
            numberedTransitions(
                context.post,
                locId.id - 1,
                0)) // TODO: This is the exit location. Should it be the current locaion?
    if (verbose) println("Invariant: $invariant")
  }

  private fun transitionForStatements(
      statements: List<Statement>,
      locId: LocationID = LocationID(0)
  ): BooleanExpression {
    return statements
        .map { transitionForStatement(it, locId) }
        .reduceOrDefault(True) { acc, next -> Or(acc, next) }
  }

  // TODO: Make this a function per statement type

  @Suppress("DuplicatedCode")
  private fun transitionForStatement(
      statement: Statement,
      locId: LocationID = LocationID(0)
  ): BooleanExpression {
    return when (statement) {
      // If case: We have to distinguish between the then and else case and handle the bodies
      is IfThenElse -> {
        val startId = locId.id
        val ifTrueTransition =
            And(
                Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
                And(
                    Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
                    And(
                        statement.cond,
                        vars
                            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                            .reduceOrDefault(True) { acc, next -> And(acc, next) })))
        var thenBody = transitionForStatements(statement.thenBlock.statements, locId)
        val lastIdThenBody = locId.id
        val ifFalseTransition =
            And(
                Eq(ValAtAddr(Variable("loc")), NumericLiteral((startId).toBigInteger()), 0),
                And(
                    Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
                    And(
                        Not(statement.cond),
                        vars
                            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                            .reduceOrDefault(True) { acc, next -> And(acc, next) })))
        val elseBody = transitionForStatements(statement.elseBlock.statements, locId)
        // Changing last location id from the when-branch (currently in locId) to the last location
        // id from the else-branch
        thenBody = changeLocation(thenBody, lastIdThenBody, locId.id)

        Or( // Return
            Or(ifTrueTransition, thenBody), Or(ifFalseTransition, elseBody))
      }
      // While case: We have to distinguish between the loop body and the next step
      is While -> {
        val startId = locId.id
        val whileTrueTransition =
            And(
                Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
                And(
                    Eq(ValAtAddr(Variable("loc'")), NumericLiteral((locId.id).toBigInteger()), 0),
                    And(
                        statement.head,
                        vars
                            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                            .reduceOrDefault(True) { acc, next -> And(acc, next) })))
        val loopBody =
            changeLocation(
                transitionForStatements(statement.body.statements, locId), locId.id, startId)
        val whileFalseTransition =
            And(
                Eq(ValAtAddr(Variable("loc")), NumericLiteral(startId.toBigInteger()), 0),
                And(
                    Eq(ValAtAddr(Variable("loc'")), NumericLiteral(locId.id.toBigInteger()), 0),
                    And(
                        Not(statement.head),
                        vars
                            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                            .reduceOrDefault(True) { acc, next -> And(acc, next) })))
        Or( // Return
            whileTrueTransition, Or(loopBody, whileFalseTransition))
      }
      // Everything else is a single step transition: Assignment, Swap, Assertion, Print, Havoc
      else ->
          And(
              Eq(ValAtAddr(Variable("loc")), NumericLiteral((locId.id++).toBigInteger()), 0),
              And(
                  Eq(ValAtAddr(Variable("loc'")), NumericLiteral(locId.id.toBigInteger()), 0),
                  when (statement) {
                    is Assignment ->
                        And(
                            Eq(statement.expr, ValAtAddr(Variable("${statement.addr}'")), 0),
                            vars
                                .filter { it != statement.addr.toString() }
                                .map {
                                  Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0)
                                }
                                .reduceOrDefault(True) { acc, next -> And(acc, next) })
                    is Swap ->
                        And(
                            Eq(
                                ValAtAddr(Variable("${statement.left}")),
                                ValAtAddr(Variable("${statement.right}'")),
                                0),
                            And(
                                Eq(
                                    ValAtAddr(Variable("${statement.right}")),
                                    ValAtAddr(Variable("${statement.left}'")),
                                    0),
                                vars
                                    .filter {
                                      it != statement.left.toString() &&
                                          it != statement.right.toString()
                                    }
                                    .map {
                                      Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0)
                                    }
                                    .reduceOrDefault(True) { acc, next ->
                                      And(acc, next)
                                    }) // TODO: Maybe remove additional "True" if there are only two
                            // variables?
                            )
                    is Assertion ->
                        And(
                            statement.cond,
                            vars
                                .map {
                                  Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0)
                                }
                                .reduceOrDefault(True) { acc, next -> And(acc, next) })
                    is Print ->
                        vars
                            .map { Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0) }
                            .reduceOrDefault(True) { acc, next -> And(acc, next) }
                    is Havoc ->
                        And(
                            Lte(
                                NumericLiteral(statement.lower),
                                ValAtAddr(Variable("${statement.addr}'"))),
                            And(
                                Lt(
                                    ValAtAddr(Variable("${statement.addr}'")),
                                    NumericLiteral(statement.upper)),
                                vars
                                    .filter { it != statement.addr.toString() }
                                    .map {
                                      Eq(ValAtAddr(Variable(it)), ValAtAddr(Variable("${it}'")), 0)
                                    }
                                    .reduceOrDefault(True) { acc, next -> And(acc, next) }))
                    else -> False
                  } // TODO: What about fail? Are there other statements? I dont think so.
                  ))
    }
  }

  // TODO: Clean this up! It works, but is not very readable. (And operations like Gt, Gte, etc. are
  // missing for invariant)

  private fun changeLocation(
      expr: BooleanExpression,
      currentId: Int,
      newId: Int
  ): BooleanExpression {
    return when (expr) {
      is Eq -> {
        if (expr.left is ValAtAddr &&
            ((expr.left.addr as Variable).name == "loc" || expr.left.addr.name == "loc'") &&
            expr.right is NumericLiteral &&
            expr.right.literal == currentId.toBigInteger()) {
          Eq(ValAtAddr(Variable(expr.left.addr.name)), NumericLiteral(newId.toBigInteger()), 0)
        } else {
          expr
        }
      }
      is And ->
          And(
              changeLocation(expr.left, currentId, newId),
              changeLocation(expr.right, currentId, newId))
      is Or ->
          Or(
              changeLocation(expr.left, currentId, newId),
              changeLocation(expr.right, currentId, newId))
      is Not -> Not(changeLocation(expr.negated, currentId, newId))
      else -> expr // Other expressions are not handled here
    }
  }

  fun numberedTransitions(from: Int, to: Int): BooleanExpression {
    return numberedTransitions(transitions, from, to)
  }

  fun zeroedInitial(from: Int = 0): BooleanExpression {
    return numberedTransitions(initial, from, from)
  }

  fun numberedInvariant(loc: Int): BooleanExpression {
    return numberedInvariant(invariant, loc)
  }

  private fun numberedInvariant(expr: BooleanExpression, loc: Int): BooleanExpression {
    return when (expr) {
      is Eq ->
          Eq(
              if (expr.left is ValAtAddr &&
                  expr.left.addr is Variable &&
                  expr.left.addr.name == "loc") {
                ValAtAddr(Variable("loc$loc"))
              } else {
                expr.left
              },
              if (expr.right is ValAtAddr &&
                  expr.right.addr is Variable &&
                  expr.right.addr.name == "loc") {
                ValAtAddr(Variable("loc$loc"))
              } else {
                expr.right
              },
              0)
      is And -> And(numberedInvariant(expr.left, loc), numberedInvariant(expr.right, loc))
      is Or -> Or(numberedInvariant(expr.left, loc), numberedInvariant(expr.right, loc))
      is Not -> Not(numberedInvariant(expr.negated, loc))
      else -> expr // Other expressions are not handled here
    }
  }

  private fun numberedTransitions(expr: BooleanExpression, from: Int, to: Int): BooleanExpression {
    return when (expr) {
      is Eq ->
          Eq(
              if (expr.left is ValAtAddr && expr.left.addr is Variable) {
                if (expr.left.addr.name.contains("'")) {
                  ValAtAddr(Variable("${expr.left.addr.name.replace("'", "")}${to}"))
                } else {
                  ValAtAddr(Variable("${expr.left.addr.name}${from}"))
                }
              } else {
                expr.left
              },
              if (expr.right is ValAtAddr && expr.right.addr is Variable) {
                if (expr.right.addr.name.contains("'")) {
                  ValAtAddr(Variable("${expr.right.addr.name.replace("'", "")}${to}"))
                } else {
                  ValAtAddr(Variable("${expr.right.addr.name}${from}"))
                }
              } else {
                expr.right
              },
              0)
      is Lt ->
          Lt(
              if (expr.left is ValAtAddr && expr.left.addr is Variable) {
                if (expr.left.addr.name.contains("'")) {
                  ValAtAddr(Variable("${expr.left.addr.name.replace("'", "")}${to}"))
                } else {
                  ValAtAddr(Variable("${expr.left.addr.name}${from}"))
                }
              } else {
                expr.left
              },
              if (expr.right is ValAtAddr && expr.right.addr is Variable) {
                if (expr.right.addr.name.contains("'")) {
                  ValAtAddr(Variable("${expr.right.addr.name.replace("'", "")}${to}"))
                } else {
                  ValAtAddr(Variable("${expr.right.addr.name}${from}"))
                }
              } else {
                expr.right
              })
      is Lte ->
          Lte(
              if (expr.left is ValAtAddr && expr.left.addr is Variable) {
                if (expr.left.addr.name.contains("'")) {
                  ValAtAddr(Variable("${expr.left.addr.name.replace("'", "")}${to}"))
                } else {
                  ValAtAddr(Variable("${expr.left.addr.name}${from}"))
                }
              } else {
                expr.left
              },
              if (expr.right is ValAtAddr && expr.right.addr is Variable) {
                if (expr.right.addr.name.contains("'")) {
                  ValAtAddr(Variable("${expr.right.addr.name.replace("'", "")}${to}"))
                } else {
                  ValAtAddr(Variable("${expr.right.addr.name}${from}"))
                }
              } else {
                expr.right
              })
      is And ->
          And(numberedTransitions(expr.left, from, to), numberedTransitions(expr.right, from, to))
      is Or ->
          Or(numberedTransitions(expr.left, from, to), numberedTransitions(expr.right, from, to))
      is Not -> Not(numberedTransitions(expr.negated, from, to))
      else -> expr // Other expressions are not handled here
    }
  }
}
