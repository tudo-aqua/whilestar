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
import tools.aqua.wvm.language.BooleanExpression
import tools.aqua.wvm.language.Not
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
                "Base case failed. ${k-1}-safety does not hold. Counterexample: ${baseResult.model.toSortedMap()}"
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
    
    fun checkWithBMC(kBound: Int = 10): Boolean {
        // Start with BMC 0:
        out.println("=== BMC 0 ===")
        val bmc0 = And(transitionSystem.zeroedInitial(), Not(transitionSystem.numberedInvariant(0)))
        if (verbose) out.println("SMT test for BMC 0: $bmc0")
        val bmc0Result = SMTSolver().solve(bmc0)
        out.println(
            when (bmc0Result.status) {
              SatStatus.UNSAT -> "BMC 0 passed."
              SatStatus.SAT ->
                  "BMC 0 failed. 0-safety does not hold. Counterexample: ${bmc0Result.model.toSortedMap()}"
              SatStatus.UNKNOWN -> "BMC 0 could not be decided."
              SatStatus.PENDING -> "Error during SMT solving of BMC 0."
            })
        if (bmc0Result.status != SatStatus.UNSAT) return false

        // ----------------------------------------

        var test: BooleanExpression = True

        for (k in 1..kBound) {
            out.println("=== K-Induction with BMC, k = $k ===")
            test = And(test, And(transitionSystem.numberedTransitions(k-1, k), transitionSystem.numberedInvariant(k-1)))
            val property = transitionSystem.numberedInvariant(k)
            // BMC-k and also already k-induction basis for k+1
            val basis = And(test, And(transitionSystem.zeroedInitial(), Not(property)))
            if (verbose) out.println("SMT test for BMC-$k / $k-induction basis: $basis")
            var result = SMTSolver().solve(basis)
            out.println(
                when (result.status) {
                    SatStatus.UNSAT -> "BMC-$k / $k-induction basis passed."
                    SatStatus.SAT -> "BMC-$k failed. Counterexample: ${result.model.toSortedMap()}"
                    SatStatus.UNKNOWN -> "BMC / $k-induction basis could not be decided."
                    SatStatus.PENDING -> "Error during SMT solving of BMC / $k-induction basis."
                })
            if (result.status != SatStatus.UNSAT) return false
            // Depth check for (k+1)-induction step
            result = SMTSolver().solve(test)
            out.println(
                when (result.status) {
                    SatStatus.SAT -> "Depth check passed."
                    SatStatus.UNSAT -> "Depth check failed. Program may be shorter than k = $k."
                    SatStatus.UNKNOWN -> "Depth check could not be decided."
                    SatStatus.PENDING -> "Error during SMT solving of depth check."
                })
            if (result.status != SatStatus.SAT) return false
            // k-induction step
            val step = And(test, Not(property))
            if (verbose) out.println("SMT test for $k-induction step: $step")
            result = SMTSolver().solve(step)
            out.println(
                when (result.status) {
                    SatStatus.UNSAT -> "Inductive step passed. Program is safe by k-induction with k = $k."
                    SatStatus.SAT -> "Inductive step failed. Could not prove safety with k = $k. Counterexample: ${result.model.toSortedMap()}"
                    SatStatus.UNKNOWN -> "Inductive step could not be decided."
                    SatStatus.PENDING -> "Error during SMT solving of inductive step."
                })
            if (result.status == SatStatus.UNSAT) return true
        }
        return false  // could not prove safety
    }

}
