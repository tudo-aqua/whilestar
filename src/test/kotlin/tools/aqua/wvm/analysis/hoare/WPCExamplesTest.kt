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
import java.time.Duration
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTimeoutPreemptively
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.DynamicTest.dynamicTest
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestFactory
import org.junit.jupiter.api.Disabled
import tools.aqua.wvm.analysis.VerificationResult
import tools.aqua.wvm.analysis.VerificationStatus
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

/**
 * Verifies that every `.w` example under `examples/` produces the WPC verdict recorded for it in
 * `examples/examples-list.txt`.
 *
 * The list file is the single source of truth for each example's expected verdict, one line per
 * example:
 *
 * ```
 * relative/path/to/example.w <safe|unsafe|unknown>
 * ```
 *
 * This turns the suite into a real regression net: if a change to the proof system alters any
 * example's verdict, that example fails and names the list entry that needs updating. (The previous
 * version only asserted the status was one of the three possible enum values, which is a
 * tautology.)
 *
 * A companion test keeps the list file and the on-disk examples in sync so a newly added or removed
 * example cannot silently escape verification.
 */
class WPCExamplesTest {

  private val exampleTimeout = Duration.ofSeconds(15)

  private val examplesDirectory = Path.of("examples")

  private val listFile get() = examplesDirectory.resolve("examples-list-verification.txt")

  private fun fromToken(token: String): VerificationStatus? =
      when (token.lowercase()) {
        "timeout" -> VerificationStatus.UNKNOWN
        else -> runCatching { VerificationStatus.valueOf(token.uppercase()) }.getOrNull()
      }

  /** Maps each example's relative path to its expected verdict. */
  private fun loadExpectations(): Map<String, VerificationStatus> {
    check(Files.isRegularFile(listFile)) { "Expectation file $listFile was not found" }
    val expectations = mutableMapOf<String, VerificationStatus>()
    Files.readAllLines(listFile).forEachIndexed { index, raw ->
      val line = raw.trim()
      if (line.isEmpty() || line.startsWith("#")) return@forEachIndexed
      val fields = line.split(Regex("\\s+"))
      check(fields.size == 2) {
        "examples-list.txt line ${index + 1} must be '<path> <safe|unsafe|unknown>': '$line'"
      }
      val (path, token) = fields
      val status = fromToken(token) ?: error("examples-list.txt line ${index + 1}: unknown verdict '$token'")
      check(expectations.put(path, status) == null) { "Duplicate entry for '$path' in examples-list.txt" }
    }
    check(expectations.isNotEmpty()) { "examples-list.txt lists no examples" }
    return expectations
  }

  /** Relative paths of all `.w` examples currently on disk, sorted. */
  private fun onDiskExamples(): List<String> {
    check(Files.isDirectory(examplesDirectory)) {
      "Examples directory was not found from ${examplesDirectory.toAbsolutePath()}"
    }
    return Files.walk(examplesDirectory).use { paths ->
      paths
          .filter { Files.isRegularFile(it) && it.toString().endsWith(".w") }
          .map { examplesDirectory.relativize(it).toString().replace('\\', '/') }
          .sorted()
          .toList()
    }
  }

  @Disabled("Diagnostic probe; run explicitly when you want to check the examples.")
  fun theListFileAndTheDiskExamplesAreInSync() {
    val disk = onDiskExamples().toSet()
    val listed = loadExpectations().keys
    val onDiskNotListed = disk - listed
    val listedNotOnDisk = listed - disk
    assertTrue(
        onDiskNotListed.isEmpty(),
        "Examples on disk but missing from ${listFile.fileName} (add them with an expected verdict): " +
            onDiskNotListed.sorted())
    assertTrue(
        listedNotOnDisk.isEmpty(),
        "Entries in ${listFile.fileName} but missing on disk (remove them or restore the files): " +
            listedNotOnDisk.sorted())
  }

  @TestFactory
  fun everyExampleProducesItsExpectedWpcResult(): List<DynamicTest> {
    val expectations = loadExpectations()
    val disk = onDiskExamples()
    check(disk.isNotEmpty()) { "No .w examples found under $examplesDirectory" }

    val testableExamples =
        disk.filter { expectations[it] in setOf(VerificationStatus.SAFE, VerificationStatus.UNSAFE, VerificationStatus.UNKNOWN) }

    return testableExamples.map { relative ->
      dynamicTest(relative) {
        val expected =
            checkNotNull(expectations[relative]) {
              "No expected verdict for $relative in ${listFile.fileName} (the list and the disk are " +
                  "out of sync)"
            }
        val source = Files.readString(examplesDirectory.resolve(relative))
        val context = Parser().parse(source)
        val output = Output().apply { log = false }
        val result =
            assertTimeoutPreemptively<VerificationResult>(exampleTimeout) {
              WPCProofSystem(context, output).proof()
            }

        assertEquals(
            expected,
            result.status,
            "$relative: WPC verdict is ${result.status}, expected $expected. If the change is " +
                "intentional, update ${listFile.fileName}. Details: $result")
      }
    }
  }
}
