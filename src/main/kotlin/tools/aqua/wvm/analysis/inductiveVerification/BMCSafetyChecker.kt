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
import tools.aqua.wvm.analysis.VerificationResult
import tools.aqua.wvm.analysis.VerificationStatus
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
   * @return A concrete counterexample, or UNKNOWN if no counterexample is found within the bound.
   */
  fun check(): VerificationResult {
    return try {
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
        val smtResult =
            try {
              SMTSolver().solve(test.smtTest())
            } catch (e: Exception) {
              val result =
                  VerificationResult(
                      VerificationStatus.UNKNOWN,
                      "SMT solving failed at bound $bound.",
                      bound,
                      e.message ?: e.javaClass.simpleName)
              out.println("BMC result: $result")
              return result
            }
        val result =
            when (smtResult.status) {
              SatStatus.UNSAT -> null
              SatStatus.SAT ->
                  VerificationResult(
                      VerificationStatus.UNSAFE,
                      "Counterexample found.",
                      bound,
                      "Counterexample: ${smtResult.modelText()}")
              SatStatus.UNKNOWN,
              SatStatus.PENDING,
              SatStatus.ERROR ->
                  VerificationResult(
                      VerificationStatus.UNKNOWN,
                      "SMT solver returned ${smtResult.status} at bound $bound.",
                      bound)
            }
        if (result != null) {
          out.println("BMC result: $result")
          return result
        }
        out.println("BMC result: $bound-safety has no counterexample.")
      }
      VerificationResult(
          VerificationStatus.UNKNOWN,
          "No counterexample found through the BMC bound; unbounded safety was not proved.",
          maxBound)
    } catch (e: Exception) {
      VerificationResult(
          VerificationStatus.UNKNOWN,
          "Could not complete bounded model checking.",
          details = e.message ?: e.javaClass.simpleName)
    }
  }
}
