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
import tools.aqua.wvm.analysis.VerificationResult.*
import tools.aqua.wvm.analysis.hoare.Entailment
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.True
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output

class BMCSafetyChecker(
    override val context: Context,
    override val out: Output = Output(),
    override val verbose: Boolean = false,
    val maxBound: Int = 100,
) : VerificationApproach {
  override val name: String = "Bounded Model Checking Safety Checker"
  val transitionSystem = TransitionSystem(context, verbose)

  override fun check(): VerificationResult {
    for (bound in 0..maxBound) {
      out.println("=== Checking ${bound}-safety: ===")
      var initAndTransitions = transitionSystem.zeroedInitial()
      if (bound > 0) {
        val transitions =
            (1..bound)
                .map { transitionSystem.numberedTransitions(it - 1, it) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) }
        initAndTransitions = And(initAndTransitions, transitions)
      }
      val properties =
          (0..bound)
              .map { transitionSystem.numberedInvariant(it) }
              .reduceOrDefault(True) { acc, next -> And(acc, next) }
      val test = Entailment(initAndTransitions, properties, "BMC safety check for bound $bound")
      if (verbose) out.println("SMT test for BMC: $test")
      val result = SMTSolver().solve(test.smtTest())

      out.println(
          "BMC result: $bound-safety " +
              when (result.status) {
                SatStatus.UNSAT -> "is fulfilled."
                SatStatus.SAT -> "is violated. Counterexample: ${result.model}"
                SatStatus.UNKNOWN -> "could not be decided.."
                SatStatus.PENDING -> "exited with an error during solving."
              })
      when (result.status) {
        SatStatus.UNSAT -> {
          /* continue checking */
        }
        SatStatus.SAT ->
            return Counterexample(
                message = "BMC: $bound-safety is violated.",
                counterexample = result.model.toString())
        SatStatus.UNKNOWN -> return Crash("BMC: $bound-safety could not be decided.")
        SatStatus.PENDING -> return Crash("BMC: $bound-safety exited with an error during solving.")
      }
    }
    return NoResult("BMC: No violation found up to bound $maxBound.")
  }
}
