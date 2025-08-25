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
import tools.aqua.wvm.analysis.hoare.Entailment
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.True
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output

/*
 * K-Induction based safety checker.
 *
 * Note: Behaves like checking from the end of the program (at least for non-looping programs).
 */
class KInductionChecker(
    val context: Context,
    val out: Output = Output(),
    val verbose: Boolean = false
) {
  val transitionSystem = TransitionSystem(context, verbose)

  fun check(kBound: Int = 10): Boolean {
    for (k in 1..kBound) {
      out.println("=== K-Induction with k = $k ===")
      // 0. Depth check
      val depthCheckTransitions =
          (2..k)
              .map { transitionSystem.numberedTransitions(it - 2, it - 1) }
              .reduceOrDefault(True) { acc, next -> And(acc, next) }
      val depthCheck = And(transitionSystem.zeroedInitial(), depthCheckTransitions)
      if (verbose) out.println("SMT test for depth check: $depthCheck")
      val depthResult = SMTSolver().solve(depthCheck)
      out.println(
          when (depthResult.status) {
            SatStatus.SAT -> "Depth check passed."
            SatStatus.UNSAT -> "Depth check failed. Program may be shorter than k = $k."
            SatStatus.UNKNOWN -> "Depth check could not be decided."
            SatStatus.PENDING -> "Error during SMT solving of depth check."
          })
      if (depthResult.status != SatStatus.SAT) return false

      // 1. Base case (== (k-1)-safety)
      val properties =
          (0..k - 1)
              .map { transitionSystem.numberedInvariant(it) }
              .reduceOrDefault(True) { acc, next -> And(acc, next) }
      val basis = Entailment(depthCheck, properties, "K-Induction base case for k = $k")
      if (verbose) out.println("SMT test for base case: $basis")
      val baseResult = SMTSolver().solve(basis.smtTest())
      out.println(
          when (baseResult.status) {
            SatStatus.UNSAT -> "Base case passed."
            SatStatus.SAT ->
                "Base case failed. ${k-1}-safety does not hold. Counterexample: ${baseResult.model}"
            SatStatus.UNKNOWN -> "Base case could not be decided."
            SatStatus.PENDING -> "Error during SMT solving of base case."
          })
      if (baseResult.status != SatStatus.UNSAT) return false

      // 2. Inductive step
      val kDepthTransitions =
          (1..k)
              .map { transitionSystem.numberedTransitions(it - 1, it) }
              .reduceOrDefault(True) { acc, next -> And(acc, next) }
      val step =
          Entailment(
              And(kDepthTransitions, properties),
              transitionSystem.numberedInvariant(k),
              "K-Induction step for k = $k")
      if (verbose) out.println("SMT test for inductive step: $step")
      val stepResult = SMTSolver().solve(step.smtTest())
      out.println(
          when (stepResult.status) {
            SatStatus.UNSAT -> "Inductive step passed. Program is safe by k-induction with k = $k."
            SatStatus.SAT ->
                "Inductive step failed. Could not prove safety with k = $k. Counterexample: ${stepResult.model.toSortedMap()}"
            SatStatus.UNKNOWN -> "Inductive step could not be decided."
            SatStatus.PENDING -> "Error during SMT solving of inductive step."
          })
      if (stepResult.status == SatStatus.UNSAT) return true
    }

    return false // could not prove safety for any k <= kBound
  }
}
