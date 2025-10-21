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

import tools.aqua.wvm.analysis.inductiveVerification.BMCSafetyChecker
import tools.aqua.wvm.machine.Context

val approaches = listOf<(Context) -> VerificationApproach> { ctx -> BMCSafetyChecker(ctx) }
val examples =
    listOf<VerificationExample>(
        VerificationExample(
            "GPDR Example 2", "examples/gpdr-examples/ex2.w", VerificationResult.Counterexample()),
        // VerificationExample("While Example 1", "examples/while/ex1.w",
        // VerificationResult.Counterexample())
    )

class BenchmarkTools {
  /*
  Many TODOs:
  - TODO: Sampling: warmupRuns, Measured runs
  - TODO: Timeout handling withTimeout(...) {...}
  - TODO: Data class AggregatedResults to hold everything
  - TODO: Memory usage
  - TODO: Number of SMT calls
  - TODO: True / False  positives/negatives classification
   */
  fun runAll() {
    for (example in examples) {
      for (approach in approaches) {
        val approach = approach(example.context)
        println("total ${ Runtime.getRuntime().totalMemory()}")
        var mem = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()
        println(mem)
        val result = approach.check()
        mem = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory() - mem
        println(mem)
        println("Example: ${example.name}, Approach: ${approach.name}, Result: ${result.message}")
      }
    }
  }
}

fun main() {
  val benchmarkTools = BenchmarkTools()
  benchmarkTools.runAll()
}
