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

import java.math.BigInteger
import kotlin.toBigInteger
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.util.reduceOrDefault
import tools.aqua.wvm.analysis.VerificationApproach
import tools.aqua.wvm.analysis.VerificationResult
import tools.aqua.wvm.analysis.hoare.Entailment
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.language.Add
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.AnyArray
import tools.aqua.wvm.language.ArrayRead
import tools.aqua.wvm.language.BasicType
import tools.aqua.wvm.language.BooleanExpression
import tools.aqua.wvm.language.Eq
import tools.aqua.wvm.language.Gte
import tools.aqua.wvm.language.Lt
import tools.aqua.wvm.language.Not
import tools.aqua.wvm.language.NumericLiteral
import tools.aqua.wvm.language.Or
import tools.aqua.wvm.language.True
import tools.aqua.wvm.language.ValAtAddr
import tools.aqua.wvm.language.Variable
import tools.aqua.wvm.language.renameVariables
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output

/**
 * GPDR verification approach. Cases: booleanEvaluation = true/false, useArrayTransitionSystem =
 * true/false
 * - useArrayTransitionSystem = false: No arrays, all variables are directly modelled. Arrays and
 *   Pointers NOT POSSIBLE! (No way to model them)
 * - booleanEvaluation = true: Variables and pointers restrained to memory size.
 *
 * TODO: Very weird edge-case: two consecutive prints, in a safe program, cause running infinitely.
 *   Look at pointer/ex1.w
 */
class GPDR(
    override val context: Context,
    override val out: Output = Output(),
    override val verbose: Boolean = false,
    val booleanEvaluation: Boolean = false,
    val useArrayTransitionSystem: Boolean = true,
    val doApproxRefinementChecks: Boolean = false,
    val doInitialSatisfiableTest: Boolean = false,
    val bound: Int = 100
) : VerificationApproach {
  override val name: String =
      "GPDR${if (booleanEvaluation) " (Boolean Evaluation)" else ""} ${if (!useArrayTransitionSystem) " (No Arrays)" else ""}"
  val transitionSystem: TransitionSystem =
      if (useArrayTransitionSystem) TransitionSystem(context, verbose)
      else TransitionSystemNoArrays(context, verbose)

  val initial = transitionSystem.initial
  var safety = transitionSystem.invariant // Safety property S

  val booleanVariableConstraint: BooleanExpression =
      transitionSystem.context.scope.symbols
          .map {
            listOf(
                    Gte(
                        ValAtAddr(Variable(it.key)),
                        NumericLiteral(
                            0.toBigInteger())), // May be fixed for "normal" integer variables
                    Lt(
                        ValAtAddr(Variable(it.key)),
                        NumericLiteral(
                            (if (useArrayTransitionSystem) transitionSystem.memorySize else 2)
                                .toBigInteger())),
                    if (useArrayTransitionSystem &&
                        booleanEvaluation &&
                        it.value.type == BasicType.INT)
                        Lt( // Constrain normal variables to be boolean,
                            ValAtAddr(ArrayRead(AnyArray, ValAtAddr(Variable(it.key)))),
                            NumericLiteral(2.toBigInteger()))
                    else True)
                .reduceOrDefault(True) { acc, next -> And(acc, next) }
          }
          .reduceOrDefault(True) { acc, next -> And(acc, next) }
  val booleanMemoryConstraint: BooleanExpression =
      if (useArrayTransitionSystem) {
        (0..transitionSystem.memorySize - 1)
            .map {
              And(
                  Gte(
                      ValAtAddr(ArrayRead(AnyArray, NumericLiteral(it.toBigInteger()))),
                      NumericLiteral(0.toBigInteger())),
                  Lt(
                      ValAtAddr(ArrayRead(AnyArray, NumericLiteral(it.toBigInteger()))),
                      NumericLiteral(transitionSystem.memorySize.toBigInteger())))
            }
            .reduceOrDefault(True) { acc, next -> And(acc, next) }
      } else True
  val locConstraint = Gte(ValAtAddr(Variable("loc")), NumericLiteral(0.toBigInteger()))
  val booleanEvaluationConstraint =
      And(And(booleanVariableConstraint, booleanMemoryConstraint), locConstraint)
  val booleanEvaluationConstraintStep =
      booleanEvaluationConstraint.renameVariables(
          transitionSystem.vars.plus("loc").plus("M").associateWith { "${it}0" })

  // R_0, R_1, ... are a sequence of over-approximations of the reachable states (in i or fewer
  // steps)

  // Invariants:
  // R_i under-approximates S: {R_i} \subseteq {S}
  // R_{i+1} over-approximates R_i and predicateTransform(R_i): {R_i} \subseteq {R_{i+1}},
  // {predicateTransform(R_i)} \subseteq {R_{i+1}}

  override fun check(): VerificationResult {
    if (verbose) println("Transitions: ${transitionSystem.transitions}")
    if (verbose) println("Invariant: $safety")
    // INITIALIZE
    val candidateModels: MutableList<Pair<BooleanExpression, Int>> = mutableListOf()
    val approximations: MutableList<BooleanExpression> =
        mutableListOf(initial) // initial == F(false)
    var N = 0
    var iteration = 0
    out.println("INITIALIZE: ε || [N = 0, R_0 = I]")
    // Test initial satisfiability
    if (doInitialSatisfiableTest && testEntailment(booleanEvaluationConstraint, True)) {
      out.println("System is vacuously VALID (initial state unsatisfiable).")
      return VerificationResult.Proof("System is vacuously VALID.", "Initial state unsatisfiable.")
    }
    while (iteration < bound) {
      if (verbose) out.println("--- Current Approximations")
      for (i in 0..N) {
        // approximations[i] = approximations[i].simplify()
        if (verbose) out.println("R_$i: ${approximations[i]}")
      }
      iteration += 1
      // VALID: Stop when over-approximations become inductive:
      // R_i \models R_{i+1}, return valid
      // TODO: Should it test all previous approximations?
      if ((N > 1) && testEntailment(approximations[N - 1], approximations[N - 2])) {
        out.println("System is VALID R_${N-1} models R_${N-2}.")
        return VerificationResult.Proof("System is VALID.", "R_${N-2} models R_${N-1}")
      }
      // MODEL: If <M, 0> is a candidate model, then report that S is violated
      if (!candidateModels.isEmpty() && candidateModels.first().second == 0) {
        out.println("System is INVALID. Model: ${candidateModels.first()}")
        return VerificationResult.Counterexample(
            "System is INVALID.", candidateModels.first().first.toString())
      }
      // UNFOLD: We look one step ahead as soon as we are sure that the system is safe for N steps:
      // if R_N \models S, then N := N + 1 and R_N := True
      if (testEntailment(And(approximations[N], booleanEvaluationConstraint), safety)) {
        out.println("UNFOLD: System is ${N}-safe, increasing bound.")
        approximations.add(if (booleanEvaluation) booleanEvaluationConstraint else True)
        N += 1
        continue
      }
      // INDUCTION: We may already have inductive properties in our R_i (just not strong enough for
      // our final goal) (Useful to apply immediately following UNFOLD and CONFLICT)
      if (N > 0) {
        val i = N - 1 // Rule: can be anything in 0 … N-1
        // phi can be any disjunct of a disjunction. The approximations are conjunctions of clauses.
        val phi = approximations[i]
        if ((N > 0) && testEntailment(F(phi), phi)) {
          println(
              "INDUCTION: Strengthening approximations with inductive property at level $i: $phi")
          approximations.forEachIndexed { j, it ->
            when (j) {
              in 1..N ->
                  if (!doApproxRefinementChecks || !testEntailment(approximations[j], phi)) {
                    approximations[j] = if (it is True) phi else And(it, phi)
                  }
            }
          }
          continue
        }
      }
      // CANDIDATE: Search for model that we can use as a basis for finding an interpolant:
      // if M \models R_N \wedge \not S(x), then produce candidate <M, N>
      if (candidateModels.isEmpty()) {
        val test = And(approximations[N], Not(safety)) // R_N \wedge \not S(x)
        val result = SMTSolver().solve(And(booleanEvaluationConstraint, test))
        if (result.status == SatStatus.SAT) {
          candidateModels.add(Pair(result.model.toFormula(), N))
          out.println("CANDIDATE: Model <${result.model.toFormula()}, $N>")
        } else {
          return VerificationResult.Crash("No candidate model found, but also not safe. => Error.")
        }
      }
      if (!candidateModels.isEmpty()) {
        val (model, i) = candidateModels.first()
        // Interpolant // actually: not_phi
        val step = F(approximations[i - 1])
        val phi = computeInterpolant(step, model)

        if (phi != null) { // Interpolant exists
          // CONFLICT: The model actually contains an interpolant, so refine over-approximation:
          // For 0<=i<N, given a candidate <M, i+1> and clause \phi, such that M \models \not\phi,
          // if \mathcal{F}(R_i) \models \phi, then conjoin \phi to R_j for j <= i+1
          out.println("CONFLICT: Found interpolant at level $i: $phi")
          approximations.forEachIndexed { j, it ->
            when (j) {
              in 1..i -> {
                if (!doApproxRefinementChecks || !testEntailment(approximations[j], phi)) {
                  approximations[j] = if (it is True) phi else And(it, phi)
                }
              }
            }
          }
          candidateModels.removeFirst()
        } else { // No interpolant exists
          // DECIDE: No interpolant, so back-propagate the dangerous states:
          // Candidate model <M, i+1> for 0 <= i < N, then subset \hat{x}_0 of x_0 and constants c_0
          // s. t. M, \hat{x}_0 = c_0 \models \mathcal{T}[R_i[x_0 / V]], then add candidate model
          // <\hat{x} = c_0, i> (renaming \hat{x}_0 to variables \hat{x} in V)
          val result =
              SMTSolver().solve(And(step, model.renameVariables(listOf("M").associateWith { it })))
          if (result.status == SatStatus.SAT) {
            val relevantAssignments =
                result.model
                    .filter { (k, _) -> k.endsWith("0") }
                    .mapKeys { (k, _) -> k.removeSuffix("0") }
            candidateModels.add(0, Pair(relevantAssignments.toFormula(), i - 1))
            out.println("DECIDE: Back-propagating to level ${i - 1}: $relevantAssignments")
            if (verbose) out.println("-- Candidate models: $candidateModels")
          } else {
            return VerificationResult.Crash(
                "Could not find proof or counterexample.${if (booleanEvaluation) " Could be because of booleanEvaluation." else ""}")
          }
        }
      }
    }
    return VerificationResult.NoResult(
        "Reached bound of $bound without finding proof or counterexample.")
  }

  private fun Map<String, String>.toFormula(): BooleanExpression {
    val map = this.toMutableMap()
    transitionSystem.vars.forEach {
      if (!this.containsKey(it)) map[it] = "0"
    } // Add missing variables as 0
    val memoryMapM = map.filter { it.key == "M" }.map { it.value.toMemoryMapping() }.getOrNull(0)
    val memoryMapM_ = map.filter { it.key == "M_" }.map { it.value.toMemoryMapping() }.getOrNull(0)
    val memoryMap = memoryMapM ?: memoryMapM_ ?: emptyMap()

    return map.filter { it.key != "M" && it.key != "M_" }
        .map {
          if (it.key == "loc") {
            Eq(ValAtAddr(Variable(it.key)), NumericLiteral(it.value.toBigInteger()), 0)
          } else if (memoryMap[it.value.toInt()] != null) {
            And(
                Eq(ValAtAddr(Variable(it.key)), NumericLiteral(it.value.toBigInteger()), 0),
                (0 until (context.scope.symbols[it.key]?.size ?: 1))
                    .map { offset ->
                      Eq(
                          ValAtAddr(
                              ArrayRead(
                                  AnyArray,
                                  if (offset > 0)
                                      Add(
                                          ValAtAddr(Variable(it.key)),
                                          NumericLiteral(offset.toBigInteger()))
                                  else ValAtAddr(Variable(it.key)))),
                          NumericLiteral(
                              memoryMap[it.value.toInt() + offset]?.toBigInteger()
                                  ?: BigInteger.ZERO),
                          0)
                    }
                    .reduceOrDefault(True) { acc, next -> And(acc, next) })
            // Note: Changing this to have the variable, not the index improved performance
          } else {
            Eq(ValAtAddr(Variable(it.key)), NumericLiteral(it.value.toBigInteger()), 0)
          }
        }
        .reduceOrDefault(True) { acc, next -> And(acc, next) }
  }

  private fun String.toMemoryMapping(): Map<Int, Int> {
    val mapping = mutableMapOf<Int, Int>()
    val constantRegex = """\(asConst \d+\)""".toRegex()
    val storeRegex = """\(store\s+\((.*?)\)\s+(\d+)\s+(\d+)\)""".toRegex()
    var constantMatch: MatchResult?
    var arrayString = this
    while (true) {
      constantMatch = constantRegex.matchEntire(arrayString)
      if (constantMatch != null) break
      val m = storeRegex.matchEntire(arrayString)
      mapping[m?.groups?.get(2)?.value?.toInt() as Int] = m.groups[3]?.value?.toInt()!!
      arrayString = "(" + m.groups[1]?.value + ")"
    }
    val constantNumber = constantMatch.value.removePrefix("(asConst ").removeSuffix(")").toInt()
    val memorySize =
        context.scope.symbols
            .map { it.value.size }
            .reduceOrDefault(0) { acc, next -> acc + next } // size of memory M
    return (0 until memorySize).associateWith { mapping[it] ?: constantNumber }
  }

  private fun testEntailment(
      left: BooleanExpression,
      right: BooleanExpression,
      booleanEvaluation: Boolean = this.booleanEvaluation
  ): Boolean {
    val leftSide = if (booleanEvaluation) And(left, booleanEvaluationConstraint) else left
    val result = SMTSolver().solve(Entailment(leftSide, right, "Entailment test").smtTest())
    return result.status == SatStatus.UNSAT
  }

  private fun computeInterpolant(
      left: BooleanExpression,
      right: BooleanExpression,
      booleanEvaluation: Boolean = this.booleanEvaluation
  ): BooleanExpression? {
    val leftSide =
        if (!booleanEvaluation) left
        else
            And(
                left,
                And(
                    booleanEvaluationConstraint.renameVariables(
                        listOf("M").associateWith { it }), // NamedArrays, not AnyArray
                    booleanEvaluationConstraintStep))
    return SMTSolver()
        .computeInterpolant(
            leftSide,
            right.renameVariables(listOf("M").associateWith { it }),
            booleanEvaluation = true)
  }

  private fun F(
      R: BooleanExpression,
      vars: List<String> = transitionSystem.vars
  ): BooleanExpression = predicateTransform(R, vars)

  private fun predicateTransform(R: BooleanExpression, vars: List<String>): BooleanExpression {
    // \mathcal{F}(R)(V) := ∃x_0. I ∨ (R[x_0 / V] ∧ \Gamma[x_0 / V][V / V′])
    return Or(
        initial.renameVariables(listOf("M").associateWith { it }),
        And(
            R.renameVariables(vars.plus("loc").plus("M").associateWith { "${it}0" }),
            transitionSystem.transitions.renameVariables(
                vars.plus("loc").plus("M").associateWith { "${it}0" } +
                    vars
                        .plus("loc")
                        .plus("M")
                        .map { "${it}'" }
                        .associateWith { it.removeSuffix("'") })))
  }
}
