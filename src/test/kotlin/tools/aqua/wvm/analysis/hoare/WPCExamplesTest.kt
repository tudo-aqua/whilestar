/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2026 The While* Authors
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

package tools.aqua.wvm.analysis.hoare

import java.nio.file.Files
import java.nio.file.Path
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.DynamicTest.dynamicTest
import org.junit.jupiter.api.TestFactory
import tools.aqua.wvm.analysis.VerificationStatus
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

class WPCExamplesTest {

  @TestFactory
  fun everyExampleProducesADecidedWpcResult(): List<DynamicTest> {
    val examplesDirectory = Path.of("examples")
    check(Files.isDirectory(examplesDirectory)) {
      "Examples directory was not found from ${Path.of("").toAbsolutePath()}"
    }
    val examples =
        Files.walk(examplesDirectory).use { paths ->
          paths.filter { Files.isRegularFile(it) && it.toString().endsWith(".w") }.sorted().toList()
        }
    check(examples.isNotEmpty()) { "No .w examples found under $examplesDirectory" }

    return examples.map { example ->
      val relativePath = examplesDirectory.relativize(example).toString().replace('\\', '/')
      dynamicTest(relativePath) {
        val source = Files.readString(example)
        val context = Parser().parse(source)
        val output = Output().apply { log = false }
        val result = WPCProofSystem(context, output).proof()

        org.junit.jupiter.api.Assertions.assertTrue(
            result.status == VerificationStatus.SAFE || result.status == VerificationStatus.UNSAFE,
            "WPC could not decide $relativePath: $result")
      }
    }
  }
}
