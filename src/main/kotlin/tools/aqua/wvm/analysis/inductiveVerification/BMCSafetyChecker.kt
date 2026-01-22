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

/**
 * Bounded Model Checking (BMC) for While* programs.
 *
 * Safety of a program is checked up to a maximum bound by unrolling the transition system.
 *
 * @property context The context containing the program and its specifications.
 * @property out The output stream for logging results.
 * @property verbose Flag to enable verbose logging.
 * @property maxBound The maximum bound up to which to check the safety property.
 */
class BMCSafetyChecker(
    val context: Context,
    val out: Output = Output(),
    val verbose: Boolean = false,
    val maxBound: Int = 100,
) {
  val transitionSystem = TransitionSystem(context, verbose)

  /**
   * The function that performs the BMC safety check.
   *
   * @return `true` if a counterexample is found (safety is violated), `false` otherwise.
   */
  fun check(): Boolean {
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
        SatStatus.UNSAT -> {} // Continue checking
        SatStatus.SAT -> true
        SatStatus.UNKNOWN -> false
        SatStatus.PENDING -> false
      }
    }
    return false
  }
}
