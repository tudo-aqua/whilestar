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

import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.util.reduceOrDefault
import tools.aqua.wvm.analysis.hoare.Entailment
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.True
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output

class BMCSafetyChecker(
    val context: Context,
    val out: Output = Output(),
    val verbose: Boolean = false
) {
  val transitionSystem = TransitionSystem(context, verbose)

  fun check(max_bound: Int = 10): Boolean {
    var success = true

    for (bound in 0..max_bound) {
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

      success = success and (result.status == SatStatus.UNSAT)
      out.println(
          "BMC result: $bound-safety " +
              when (result.status) {
                SatStatus.UNSAT -> "is fulfilled."
                SatStatus.SAT -> "is violated. Counterexample: ${result.model}"
                SatStatus.UNKNOWN -> "could not be decided.."
                SatStatus.PENDING -> "exited with an error during solving."
              })
      if (result.status != SatStatus.UNSAT) {
        success = false
      }
      if (!success) break
    }

    return success
  }
}
