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

package tools.aqua.wvm.analysis

import java.io.File
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import kotlin.system.measureTimeMillis
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.analysis.hoare.WPCProofSystem
import tools.aqua.wvm.analysis.inductiveVerification.BMCSafetyChecker
import tools.aqua.wvm.analysis.inductiveVerification.GPDR
import tools.aqua.wvm.analysis.inductiveVerification.KInductionChecker
import tools.aqua.wvm.analysis.inductiveVerification.KInductionCheckerWithBMC
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output

val approaches =
    listOf<(Context) -> VerificationApproach>(
        { ctx -> BMCSafetyChecker(ctx, maxBound = 10) },
        { ctx -> KInductionChecker(ctx, kBound = 10) },
        { ctx -> KInductionCheckerWithBMC(ctx, kBound = 10) },
        { ctx -> WPCProofSystem(ctx) },
        { ctx -> GPDR(ctx, bound = 10) },
        { ctx -> GPDR(ctx, booleanEvaluation = true, bound = 10) })

val examples =
    File("examples/examples-list.txt").readLines().map { line ->
      val parts = line.split(" ")
      val path = "examples/" + parts[0].trim()
      val name = parts[1].trim()
      val expected =
          when (parts[2].trim().lowercase()) {
            "true" -> VerificationResult.Proof("Expected Proof")
            "false" -> VerificationResult.Counterexample("Expected Counterexample")
            else -> VerificationResult.NoResult("No Expected Result")
          }
      VerificationExample(name, path, expected)
    }

data class BenchmarkResult(
    val exampleName: String,
    val approachName: String,
    val timeMillis: Long,
    val memoryBytes: Long,
    val classification: String,
    val numberOfSMTCalls: Int
) {
  val allAttributes: List<Any>
    get() =
        listOf(exampleName, approachName, timeMillis, memoryBytes, classification, numberOfSMTCalls)

  companion object {
    val attributeNames: List<String>
      get() =
          listOf("Example", "Approach", "Time(ms)", "Memory(bytes)", "Classification", "#SMTCalls")
  }
}

class BenchmarkTools {
  /*
  Many TODOs:
  - TODO: Sampling: warmupRuns, Measured runs, hold aggregated results in data class
  - TODO: Timeout handling
  - TODO: Memory usage => This is not great, consider using a profiler, ask supervisor
   */
  val out = Output()

  fun runAll() {
    val allResults: MutableList<BenchmarkResult> = mutableListOf()
    for (example in examples) {
      for (a in approaches) {
        out.println(
            "--- Running example: ${example.name} with approach: ${a(example.context).name}")
        // Measure here: time, memory, ...
        Runtime.getRuntime().gc()
        val memBefore = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()
        var result: VerificationResult
        var approach: VerificationApproach? = null
        val time = measureTimeMillis {
          approach = a(example.context) // Create approach instance
          result = approach.check() // Run verification
        }
        val memAfter = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()
        Runtime.getRuntime().gc()
        val memUsed = memAfter - memBefore
        val numberOfSMTCalls = SMTSolver.numberOfSMTCalls.also { SMTSolver.resetCallCounters() }
        out.println(
            "--- Example: ${example.name}, Approach: ${approach?.name}, Result: ${result.message}")
        val benchmarkResult =
            BenchmarkResult(
                exampleName = example.name,
                approachName = approach?.name ?: "Unknown",
                timeMillis = time,
                memoryBytes = memUsed,
                classification = confusionClassification(result, example.expectedResult),
                numberOfSMTCalls = numberOfSMTCalls)
        allResults.add(benchmarkResult)
        out.println("Benchmark result: ${benchmarkResult.toString()}")
      }
    }
    saveToCSV(allResults)
  }

  fun confusionClassification(predicted: VerificationResult, expected: VerificationResult): String {
    return when {
      predicted is VerificationResult.Proof && expected is VerificationResult.Proof ->
          "True Positive"
      predicted is VerificationResult.Counterexample &&
          expected is VerificationResult.Counterexample -> "True Negative"
      predicted is VerificationResult.Proof && expected is VerificationResult.Counterexample ->
          "False Positive"
      predicted is VerificationResult.Counterexample && expected is VerificationResult.Proof ->
          "False Negative"
      else -> "No Result"
    }
  }

  fun saveToCSV(results: List<BenchmarkResult>) {
    val timestamp = LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyyMMdd-HHmmss"))
    val file = File("out/benchmark_results_$timestamp.csv")

    file.printWriter().use { out ->
      out.println(BenchmarkResult.attributeNames.joinToString(",")) // Header
      for (result in results) {
        out.println(result.allAttributes.joinToString(","))
      }
    }
  }
}

fun main() {
  val benchmarkTools = BenchmarkTools()
  benchmarkTools.runAll()
}
