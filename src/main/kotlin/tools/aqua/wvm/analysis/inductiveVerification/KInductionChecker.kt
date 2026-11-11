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
import tools.aqua.wvm.analysis.VerificationResult
import tools.aqua.wvm.analysis.VerificationStatus
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
   * @return A proof, a reachable counterexample, or UNKNOWN if the configured bound is exhausted.
   */
  fun check(): VerificationResult {
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
        // 1. Base case (== (k-1)-safety)
        val properties =
            (0..k - 1)
                .map { transitionSystem.numberedInvariant(it) }
                .reduceOrDefault(True) { acc, next -> And(acc, next) }
        val basis = Entailment(depthCheck, properties, "K-Induction base case for k = $k")
        if (verbose) out.println("SMT test for base case: $basis")
        val baseResult = solve(basis.smtTest(), "base case", k) ?: return unknown("base case", k)
        when (baseResult.status) {
          SatStatus.UNSAT -> out.println("Base case passed.")
          SatStatus.SAT ->
              return VerificationResult(
                  VerificationStatus.UNSAFE,
                  "A reachable counterexample violates the property.",
                  k - 1,
                  "Counterexample: ${baseResult.modelText()}")
          else -> return unknown("base case", k, baseResult.status)
        }

        val depthResult = solve(depthCheck, "depth check", k) ?: return unknown("depth check", k)
        when (depthResult.status) {
          SatStatus.SAT -> out.println("Depth check passed. ${depthResult.modelText()}")
          SatStatus.UNSAT ->
              return VerificationResult(
                  VerificationStatus.SAFE,
                  "The base case covers all reachable states; no longer execution exists.",
                  k - 1)
          else -> return unknown("depth check", k, depthResult.status)
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
        val stepResult =
            solve(step.smtTest(), "inductive step", k) ?: return unknown("inductive step", k)
        when (stepResult.status) {
          SatStatus.UNSAT -> {
            out.println("Inductive step passed. Program is safe by k-induction with k = $k.")
            return VerificationResult(
                VerificationStatus.SAFE, "K-induction proved the property.", k)
          }
          SatStatus.SAT ->
              out.println(
                  "Inductive step failed. Could not prove safety with k = $k. Counterexample: ${stepResult.modelText()}")
          SatStatus.UNKNOWN -> {
            return unknown("inductive step", k, stepResult.status)
          }
          SatStatus.PENDING -> {
            return unknown("inductive step", k, stepResult.status)
          }
          SatStatus.ERROR -> {
            return unknown("inductive step", k, stepResult.status)
          }
        }
      }
      return VerificationResult(
          VerificationStatus.UNKNOWN, "No induction proof found through k = $kBound.", kBound)
    } catch (e: Exception) {
      return VerificationResult(
          VerificationStatus.UNKNOWN,
          "Could not complete k-induction.",
          details = e.message ?: e.javaClass.simpleName)
    }
  }

  private fun solve(expr: BooleanExpression, stage: String, k: Int): SMTSolver.Result? =
      try {
        SMTSolver().solve(expr)
      } catch (e: Exception) {
        out.println("Solver failed during $stage at k = $k: ${e.message}")
        null
      }

  private fun unknown(stage: String, k: Int, status: SatStatus? = null) =
      VerificationResult(
          VerificationStatus.UNKNOWN,
          "K-induction could not decide the $stage${status?.let { " ($it)" } ?: ""}.",
          k)
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
   * @return A proof, a reachable counterexample, or UNKNOWN if the configured bound is exhausted.
   */
  fun check(): VerificationResult {
    try {
      // Start with BMC 0:
      out.println("=== BMC 0 ===")
      val bmc0 = And(transitionSystem.zeroedInitial(), Not(transitionSystem.numberedInvariant(0)))
      if (verbose) out.println("SMT test for BMC 0: $bmc0")
      val bmc0Result = solve(bmc0, "BMC base case", 0) ?: return unknown("BMC base case", 0)
      when (bmc0Result.status) {
        SatStatus.UNSAT -> out.println("BMC 0 passed.")
        SatStatus.SAT -> {
          return VerificationResult(
              VerificationStatus.UNSAFE,
              "A reachable counterexample violates the property.",
              0,
              "Counterexample: ${bmc0Result.modelText()}")
        }
        else -> return unknown("BMC base case", 0, bmc0Result.status)
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
        var result = solve(basis, "BMC basis", k) ?: return unknown("BMC basis", k)
        when (result.status) {
          SatStatus.UNSAT -> out.println("BMC-$k / $k-induction basis passed.")
          SatStatus.SAT -> {
            return VerificationResult(
                VerificationStatus.UNSAFE,
                "A reachable counterexample violates the property.",
                k,
                "Counterexample: ${result.modelText()}")
          }
          else -> return unknown("BMC basis", k, result.status)
        }

        // Depth check for (k+1)-induction step
        result = solve(test, "depth check", k) ?: return unknown("depth check", k)
        when (result.status) {
          SatStatus.SAT -> out.println("Depth check passed.")
          SatStatus.UNSAT ->
              return VerificationResult(
                  VerificationStatus.SAFE,
                  "The checked base covers all reachable states; no longer execution exists.",
                  k)
          else -> return unknown("depth check", k, result.status)
        }

        // k-induction step
        val step = And(test, Not(property))
        if (verbose) out.println("SMT test for $k-induction step: $step")
        result = solve(step, "inductive step", k) ?: return unknown("inductive step", k)
        when (result.status) {
          SatStatus.UNSAT -> {
            out.println("Inductive step passed. Program is safe by k-induction with k = $k.")
            return VerificationResult(
                VerificationStatus.SAFE, "K-induction proved the property.", k)
          }
          SatStatus.SAT ->
              out.println(
                  "Inductive step failed. Could not prove safety with k = $k. Counterexample: ${result.modelText()}")
          SatStatus.UNKNOWN -> {
            return unknown("inductive step", k, result.status)
          }
          SatStatus.PENDING -> {
            return unknown("inductive step", k, result.status)
          }
          SatStatus.ERROR -> {
            return unknown("inductive step", k, result.status)
          }
        }
      }
      return VerificationResult(
          VerificationStatus.UNKNOWN, "No BMC/k-induction proof found through k = $kBound.", kBound)
    } catch (e: Exception) {
      return VerificationResult(
          VerificationStatus.UNKNOWN,
          "Could not complete BMC/k-induction.",
          details = e.message ?: e.javaClass.simpleName)
    }
  }

  private fun solve(expr: BooleanExpression, stage: String, k: Int): SMTSolver.Result? =
      try {
        SMTSolver().solve(expr)
      } catch (e: Exception) {
        out.println("Solver failed during $stage at k = $k: ${e.message}")
        null
      }

  private fun unknown(stage: String, k: Int, status: SatStatus? = null) =
      VerificationResult(
          VerificationStatus.UNKNOWN,
          "BMC/k-induction could not decide the $stage${status?.let { " ($it)" } ?: ""}.",
          k)
}
