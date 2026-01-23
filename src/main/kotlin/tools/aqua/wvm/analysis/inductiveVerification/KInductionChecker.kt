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

import kotlin.Int
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

/**
 * K-Induction based safety checker for While* programs.
 *
 * @param context The program context containing the While* program to be checked.
 * @param out The output stream for logging results and information.
 * @param verbose Flag to enable verbose logging.
 * @param useWhileInvariant Flag to indicate whether to use while loop invariants in the analysis.
 * @param kBound The maximum value of k to be used in the k-induction process.
 */
class KInductionChecker(
    val context: Context,
    val out: Output = Output(),
    val verbose: Boolean = false,
    useWhileInvariant: Boolean = false,
    val kBound: Int = 100
) {
  val transitionSystem = TransitionSystem(context, verbose, useWhileInvariant)

  /**
   * Performs the k-induction safety check.
   *
   * @return true if the program is proven safe, false if a counterexample is found or the check
   *   could not be completed.
   */
  fun check(): Boolean {
    try {
      for (k in 1..kBound) {
        out.println("=== K-Induction with k = $k ===")
        // 0. Depth check (Might not even be necessary for "normal" BMC)
        val depthCheckTransitions =
            (2..k)
                .map { transitionSystem.numberedTransitions(it - 2, it - 1) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) }
        val depthCheck = And(transitionSystem.zeroedInitial(), depthCheckTransitions)
        if (verbose) out.println("SMT test for depth check: $depthCheck")
        val depthResult = SMTSolver().solve(depthCheck)
        when (depthResult.status) {
          SatStatus.SAT -> out.println("Depth check passed. ${depthResult.model.toSortedMap()}")
          SatStatus.UNSAT -> {
            out.println("Depth check failed. Program may be shorter than k = $k.")
            return true
          }
          SatStatus.UNKNOWN -> {
            out.println("Depth check at k = $k could not be decided.")
            return false
          }
          SatStatus.PENDING -> {
            out.println("Error during SMT solving of depth check at k = $k.")
            return false
          }
        }

        // 1. Base case (== (k-1)-safety)
        val properties =
            (0..k - 1)
                .map { transitionSystem.numberedInvariant(it) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) }
        val basis = Entailment(depthCheck, properties, "K-Induction base case for k = $k")
        if (verbose) out.println("SMT test for base case: $basis")
        val baseResult = SMTSolver().solve(basis.smtTest())
        when (baseResult.status) {
          SatStatus.UNSAT -> out.println("Base case passed.")
          SatStatus.SAT -> {
            out.println(
                "Base case failed. ${k-1}-safety does not hold. Counterexample: ${baseResult.model.toSortedMap()}")
            return false
          }
          SatStatus.UNKNOWN -> {
            out.println("Base case could not be decided.")
            return false
          }
          SatStatus.PENDING -> {
            out.println("Error during SMT solving of base case.")
            return false
          }
        }

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
        when (stepResult.status) {
          SatStatus.UNSAT -> {
            out.println("Inductive step passed. Program is safe by k-induction with k = $k.")
            return true
          }
          SatStatus.SAT ->
              out.println(
                  "Inductive step failed. Could not prove safety with k = $k. Counterexample: ${stepResult.model.toSortedMap()}")
          SatStatus.UNKNOWN -> {
            out.println("Inductive step could not be decided.")
            return false
          }
          SatStatus.PENDING -> {
            out.println("Error during SMT solving of inductive step.")
            return false
          }
        }
      }
      return false
    } catch (e: RuntimeException) {
      return false
    }
  }
}

/**
 * K-Induction based safety checker with integrated Bounded Model Checking (BMC) for While*
 * programs.
 *
 * @param context The program context containing the While* program to be checked.
 * @param out The output stream for logging results and information.
 * @param verbose Flag to enable verbose logging.
 * @param useWhileInvariant Flag to indicate whether to use while loop invariants in the analysis.
 * @param kBound The maximum value of k to be used in the k-induction process.
 */
class KInductionCheckerWithBMC(
    val context: Context,
    val out: Output = Output(),
    val verbose: Boolean = false,
    useWhileInvariant: Boolean = false,
    val kBound: Int = 100
) {
  val transitionSystem = TransitionSystem(context, verbose, useWhileInvariant)

  /**
   * Performs the k-induction with BMC safety check.
   *
   * @return true if the program is proven safe, false if a counterexample is found or the check
   *   could not be completed.
   */
  fun check(): Boolean {
    try {
      // Start with BMC 0:
      out.println("=== BMC 0 ===")
      val bmc0 = And(transitionSystem.zeroedInitial(), Not(transitionSystem.numberedInvariant(0)))
      if (verbose) out.println("SMT test for BMC 0: $bmc0")
      val bmc0Result = SMTSolver().solve(bmc0)
      when (bmc0Result.status) {
        SatStatus.UNSAT -> out.println("BMC 0 passed.")
        SatStatus.SAT -> {
          out.println(
              "BMC 0 failed. 0-safety does not hold. Counterexample: ${bmc0Result.model.toSortedMap()}")
          return false
        }
        SatStatus.UNKNOWN -> {
          out.println("BMC 0 could not be decided.")
          return false
        }
        SatStatus.PENDING -> {
          out.println("Error during SMT solving of BMC 0.")
          return false
        }
      }

      // Now do k-induction with BMC up to kBound
      var test: BooleanExpression = True
      for (k in 1..kBound) {
        out.println("=== K-Induction with BMC, k = $k ===")
        test =
            And(
                test,
                And(
                    transitionSystem.numberedTransitions(k - 1, k),
                    transitionSystem.numberedInvariant(k - 1)))
        val property = transitionSystem.numberedInvariant(k)
        // BMC-k and also already k-induction basis for k+1
        val basis = And(test, And(transitionSystem.zeroedInitial(), Not(property)))
        if (verbose) out.println("SMT test for BMC-$k / $k-induction basis: $basis")
        var result = SMTSolver().solve(basis)
        when (result.status) {
          SatStatus.UNSAT -> out.println("BMC-$k / $k-induction basis passed.")
          SatStatus.SAT -> {
            out.println("BMC-$k failed. Counterexample: ${result.model.toSortedMap()}")
            return false
          }
          SatStatus.UNKNOWN -> {
            out.println("BMC / $k-induction basis could not be decided.")
            return false
          }
          SatStatus.PENDING -> {
            out.println("Error during SMT solving of BMC / $k-induction basis.")
            return false
          }
        }

        // Depth check for (k+1)-induction step
        result = SMTSolver().solve(test)
        when (result.status) {
          SatStatus.SAT -> out.println("Depth check passed.")
          SatStatus.UNSAT -> {
            out.println("Depth check failed. Program may be shorter than k = $k.")
            return true
          }
          SatStatus.UNKNOWN -> {
            out.println("Depth check at k = $k could not be decided.")
            return true
          }
          SatStatus.PENDING -> {
            out.println("Error during SMT solving of depth check at k = $k.")
            return true
          }
        }

        // k-induction step
        val step = And(test, Not(property))
        if (verbose) out.println("SMT test for $k-induction step: $step")
        result = SMTSolver().solve(step)
        when (result.status) {
          SatStatus.UNSAT -> {
            out.println("Inductive step passed. Program is safe by k-induction with k = $k.")
            return true
          }
          SatStatus.SAT ->
              out.println(
                  "Inductive step failed. Could not prove safety with k = $k. Counterexample: ${result.model.toSortedMap()}")
          SatStatus.UNKNOWN -> {
            out.println("Inductive step could not be decided.")
            return false
          }
          SatStatus.PENDING -> {
            out.println("Error during SMT solving of inductive step.")
            return false
          }
        }
      }
      return false
    } catch (e: RuntimeException) {
      return false
    }
  }
}
