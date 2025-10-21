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
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

sealed class VerificationResult {
  abstract val message: String?
  val safe: Boolean
    get() = this is Proof

  data class Proof(override val message: String? = null, val proof: String? = null) :
      VerificationResult()

  data class Counterexample(
      override val message: String? = null,
      val counterexample: String? = null
  ) : VerificationResult()

  data class NoResult(override val message: String? = null) : VerificationResult()

  data class Crash(override val message: String? = null, val exception: Throwable? = null) :
      VerificationResult()
}

interface VerificationApproach {
  val name: String
  val context: Context
  val verbose: Boolean
  val out: Output

  fun check(): VerificationResult
}

data class VerificationExample(
    val name: String,
    val programPath: String,
    val expectedResult: VerificationResult
) {
  val context = Parser.parse(File(programPath).readText())
}
