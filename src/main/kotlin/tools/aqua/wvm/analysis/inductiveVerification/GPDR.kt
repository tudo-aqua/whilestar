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

import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.util.reduceOrDefault
import tools.aqua.wvm.analysis.VerificationApproach
import tools.aqua.wvm.analysis.VerificationResult
import tools.aqua.wvm.analysis.hoare.Entailment
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.AnyArray
import tools.aqua.wvm.language.ArrayRead
import tools.aqua.wvm.language.BooleanExpression
import tools.aqua.wvm.language.Eq
import tools.aqua.wvm.language.Not
import tools.aqua.wvm.language.NumericLiteral
import tools.aqua.wvm.language.Or
import tools.aqua.wvm.language.True
import tools.aqua.wvm.language.ValAtAddr
import tools.aqua.wvm.language.Variable
import tools.aqua.wvm.language.renameVariables
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output

class GPDR(
    override val context: Context,
    override val out: Output = Output(),
    override val verbose: Boolean = false,
    val booleanEvaluation: Boolean = false,
    val bound: Int = 100
) : VerificationApproach {
  override val name: String = "GPDR${if (booleanEvaluation) " (Boolean Evaluation)" else ""}"
  val transitionSystem = TransitionSystem(context, verbose)

  val initial = transitionSystem.initial
  // And(transitionSystem.context.pre, Eq(ValAtAddr(Variable("loc")),
  // NumericLiteral(0.toBigInteger()), 0))
  // TODO: Test if initial is satisfiable at all
  var safety = transitionSystem.invariant // Safety property S

  // R_0, R_1, ... are a sequence of over-approximations of the reachable states (in i or fewer
  // steps)

  // Invariants:
  // R_i under-approximates S: {R_i} \subseteq {S}
  // R_{i+1} over-approximates R_i and predicateTransform(R_i): {R_i} \subseteq {R_{i+1}},
  // {predicateTransform(R_i)} \subseteq {R_{i+1}}

  override fun check(): VerificationResult {
    // INITIALIZE
    val candidateModels: MutableList<Pair<BooleanExpression, Int>> = mutableListOf()
    val approximations: MutableList<BooleanExpression> =
        mutableListOf(initial) // initial == F(false)
    var N = 0
    var iteration = 0
    out.println("INITIALIZE: ε || [N = 0, R_0 = I]")
    // TODO: Make sure the initial is actually reachable/satisfiable

    while (iteration < bound) {
      iteration += 1
      // VALID: Stop when over-approximations become inductive:
      // R_i \models R_{i+1}, return valid
      // TODO: Should it test all previous approximations?
      if ((N > 1) && testEntailment(approximations[N - 1], approximations[N - 2])) {
        out.println("System is VALID.")
        return VerificationResult.Proof("System is VALID.")
      }
      // MODEL: If <M, 0> is a candidate model, then report that S is violated
      if (!candidateModels.isEmpty() && candidateModels.first().second == 0) {
        out.println("System is INVALID. Model: ${candidateModels.first()}")
        return VerificationResult.Counterexample(
            "System is INVALID.", candidateModels.first().first.toString())
      }
      // UNFOLD: We look one step ahead as soon as we are sure that the system is safe for N steps:
      // if R_N \models S, then N := N + 1 and R_N := True
      if (testEntailment(approximations[N], safety)) {
        out.println("UNFOLD: System is ${N}-safe, increasing bound.")
        approximations.add(True)
        N += 1
        continue
      }
      // INDUCTION: We may already have inductive properties in our R_i (just not strong enough for
      // our final goal)
      // (Useful to apply immediately following UNFOLD and CONFLICT)
      // TODO: Check this code:
      if (N > 0 && false) {
        val i = N - 1 // TODO: can be anything in 0 … N-1
        val phi = approximations[i] // TODO: phi can be anything (?) How to choose?
        if ((N > 0) && testEntailment(F(And(approximations[i], phi)), phi)) {
          approximations.forEachIndexed { j, it ->
            when (j) {
              in 1..N -> approximations[j] = if (it is True) phi else And(it, phi)
            }
          }
        }
      }
      // CANDIDATE: Search for model that we can use as a basis for finding an interpolant:
      // if M \models R_N \wedge \not S(x), then produce candidate <M, N>
      if (candidateModels.isEmpty()) {
        val test = And(approximations[N], Not(safety)) // R_N \wedge \not S(x)
        val result = SMTSolver(booleanEvaluation).solve(test)
        if (result.status == SatStatus.SAT) {
          candidateModels.add(Pair(result.model.toFormula(), N))
          out.println("CANDIDATE: Model <${result.model.toFormula()}, $N>")
        } else {
          out.println("No candidate model found. Is the system VALID? Check this further!!") // TODO
          return VerificationResult.Crash("This should not happen. No candidate model found.")
        }
      }
      if (!candidateModels.isEmpty()) {
        val (model, i) = candidateModels.first()
        // val result =

        // Interpolant // TODO: Calculate with Z3 // actually: not_phi
        val step = F(approximations[i - 1])
        val phi = SMTSolver(booleanEvaluation).computeInterpolant(step, model)

        if (phi != null) { // interpolant exists
          // CONFLICT: If the model actually contains an interpolant, we refine our
          // over-approximation:
          // For 0 <= i < N, given a candidate model <M, i+1> and clause \phi, such that M \models
          // \not\phi,
          // if \mathcal{F}(R_i) \models \phi, then conjoin \phi to R_j for j <= i+1
          out.println("CONFLICT: Found interpolant at level $i: $phi")
          approximations.forEachIndexed { j, it ->
            when (j) {
              in 1..i -> approximations[j] = if (it is True) phi else And(it, phi)
            }
          }
          candidateModels.removeFirst()
        } else { // Not interpolant exists
          // DECIDE: In case we do not find an interpolant with the conflict rule, we have to
          // back-propagate the dangerous states:
          // If <M, i+1> for 0 <= i < N is a candidate model and there is a subset \hat{x}_0 of x_0
          // and constants c_0 such that
          // M, \hat{x}_0 = c_0 \models \mathcal{T}[R_i[x_0 / V]], then add the candidate model
          // <\hat{x} = c_0, i> (renaming \hat{x}_0 to variables \hat{x} in V)
          val test = And(model, step)
          val result = SMTSolver().solve(test)
          if (result.status == SatStatus.SAT) {
            val relevantAssignments =
                result.model
                    .filter { (k, _) -> k.endsWith("0") }
                    .mapKeys { (k, _) -> k.removeSuffix("0") }
            // TODO: Does it suffice to use a subset of the assignments?
            candidateModels.add(0, Pair(relevantAssignments.toFormula(), i - 1))
            out.println("DECIDE: Back-propagating to level ${i - 1}: $relevantAssignments")
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
    return map.map {
          when (it.key) {
            "M_", "M" -> it.value.toArrayFormula()
            else -> Eq(ValAtAddr(Variable(it.key)), NumericLiteral(it.value.toBigInteger()), 0)
          }
        }
        .reduceOrDefault(True) { acc, next -> And(acc, next) }
  }

  private fun String.toArrayFormula(): BooleanExpression {
    val regex = """\(asConst \d+\)""".toRegex()
    val match = regex.matchEntire(this)
    val number = match?.value?.removePrefix("(asConst ")?.removeSuffix(")")?.toInt() ?: 0
    val memorySize =
        context.scope.symbols
            .map { it.value.size }
            .reduceOrDefault(0) { acc, next -> acc + next } // size of memory M
    return (0 until memorySize)
        .map {
          Eq(
              ValAtAddr(ArrayRead(AnyArray, NumericLiteral(it.toBigInteger()))),
              NumericLiteral(number.toBigInteger()),
              0)
        }
        .reduceOrDefault(True) { acc, next -> And(acc, next) }
  }

  private fun testEntailment(left: BooleanExpression, right: BooleanExpression): Boolean {
    val result =
        SMTSolver(booleanEvaluation).solve(Entailment(left, right, "Entailment test").smtTest())
    return result.status == SatStatus.UNSAT
  }

  private fun F(
      R: BooleanExpression,
      vars: List<String> = transitionSystem.vars
  ): BooleanExpression = predicateTransform(R, vars)

  private fun predicateTransform(R: BooleanExpression, vars: List<String>): BooleanExpression {
    // \mathcal{F}(R)(V) := ∃x_0. I ∨ (R[x_0 / V] ∧ \Gamma[x_0 / V][V / V′])
    return Or(
        initial,
        And(
            R.renameVariables(vars.plus("loc").plus("M").associateWith { "${it}0" }),
            transitionSystem.transitions.renameVariables(
                vars.plus("loc").plus("M").associateWith { "${it}0" } +
                    vars.plus("loc").plus("M").map { "${it}'" }.associateWith { it.removeSuffix("'") })))
  }
}
