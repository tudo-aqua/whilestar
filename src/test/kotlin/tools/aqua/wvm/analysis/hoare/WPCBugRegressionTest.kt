/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2024 The While* Authors
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

import kotlin.random.Random
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tools.aqua.wvm.analysis.VerificationStatus
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

/**
 * Regression tests for four WPC proof-system bugs, plus a deterministic fuzz
 * consistency check. Each bug is documented with the *correct* expected
 * behavior. Bugs that were fixed are asserted to pass; bugs that are still open
 * on this branch are asserted against the correct behavior as well and are
 * expected to fail, thereby documenting the outstanding defect.
 */
class WPCBugRegressionTest {

  private fun proofStatus(source: String): VerificationStatus {
    val context = Parser().parse(source.trimIndent())
    val output = Output()
    output.log = false
    return WPCProofSystem(context, output).proof().status
  }

  /** Executes [source] in the interpreter and returns the final value of [varName]. */
  private fun interpValue(source: String, varName: String): Long {
    val context = Parser().parse(source.trimIndent())
    val output = Output()
    output.log = false
    val trace = context.execute(false, output, maxSteps = 100000)
    val finalCfg = trace.last().result.dst
    return finalCfg.memory.read(finalCfg.scope.resolve(varName)).toLong()
  }

  // -- Bug 1: scalar assignment combined with a pointer store ----------------
  // The proof previously lost the link between a scalar assignment and a later
  // write through a pointer, so `*p := 5` (with `p := &a`) was not propagated to
  // `a`. Fixed: the store must update the aliased scalar.

  @Test
  fun bug1_scalarAssignThenPointerStore_isSafe() {
    assertEquals(
        VerificationStatus.SAFE,
        proofStatus(
            """
            vars:
              int a;
              int *p;
            code:
              p := &a;
              a := 1;
              *p := 5;
            post: (a = 5)
            """.trimIndent()))
  }

  @Test
  fun bug1_scalarAssignThenPointerStore_wrongValue_isUnsafe() {
    // Negative control: the same store leaves a = 5, so a = 1 must be refuted.
    assertEquals(
        VerificationStatus.UNSAFE,
        proofStatus(
            """
            vars:
              int a;
              int *p;
            code:
              p := &a;
              a := 1;
              *p := 5;
            post: (a = 1)
            """.trimIndent()))
  }

  // -- Bug 2: invariant VC on a loop that is never entered -------------------
  // A weak invariant that holds at entry but whose maintenance VC fails must not
  // be reported as UNSAFE when the loop body is unreachable; the proof must be
  // classified UNKNOWN. Fixed: invariant VC failures are reclassified to UNKNOWN.

  @Test
  fun bug2_unreachableLoop_weakInvariant_isUnknown() {
    assertEquals(
        VerificationStatus.UNKNOWN,
        proofStatus(
            """
            vars:
              int x;
            code:
              x := 0;
              while (x < 0) invariant (x = 0 or x = 5) {
                x := x + 1;
              };
            post: (x = 0)
            """.trimIndent()))
  }

  @Test
  fun bug2_unreachableLoop_strongInvariant_control_isSafe() {
    // Control case: a strong invariant that is genuinely maintained still proves
    // SAFE, so the UNKNOWN reclassification is not hiding real UNSAFE results.
    assertEquals(
        VerificationStatus.SAFE,
        proofStatus(
            """
            vars:
              int x;
            code:
              x := 3;
              while (x = 1) invariant (x = 3) {
                x := x - 1;
              };
            post: (x = 3)
            """.trimIndent()))
  }


  // -- Bug 3: non-`True` precondition skips the scalar<->memory link ----------
  // `augment` used to return early when the incoming precondition was not `True`, so the
  // alias link between a scalar and a memory location was dropped.

  @Test
  fun bug3_nonTruePre_scalarAndMemoryLink_isSafe() {
    assertEquals(
        VerificationStatus.SAFE,
        proofStatus(
            """
            vars:
              int a;
              int *p;
            pre: (a = 2)
            code:
              p := &a;
              a := a + 1;
            post: (a = 3)
            """.trimIndent()))
  }

  @Test
  fun bug3_nonTruePre_unrelatedPointerStore_isSafe() {
    assertEquals(
        VerificationStatus.SAFE,
        proofStatus(
            """
            vars:
              int a;
              int b;
              int *p;
            pre: (a = 0)
            code:
              p := &b;
              *p := 5;
            post: (a = 0)
            """.trimIndent()))
  }

  @Test
  fun bug3_loopInvariant_scalarAndMemoryLink_isSafe() {
    assertEquals(
        VerificationStatus.SAFE,
        proofStatus(
            """
            vars:
              int a;
              int b;
              int *p;
            pre: (a = 0)
            code:
              while (b = 0) invariant (a = 0) {
                p := &b;
                *p := 5;
              };
            post: (a = 0)
            """.trimIndent()))
  }

  // -- Bug 4: `wpc(While)` does not validate the loop body --------------------
  // A broken invariant must not yield a weakest precondition.

  @Test
  fun bug4_brokenLoopInvariant_weakestPreconditionIsNull() {
    val context = Parser().parse(
        """
        vars:
          int x;
        code:
          x := 0;
          while (x < 3) invariant (x = 0) {
            x := x + 1;
          };
        post: (x = 3)
        """.trimIndent())
    val output = Output()
    output.log = false
    assertNull(
        WPCProofSystem(context, output).weakestPrecondition(context.post),
        "A broken loop invariant must not yield a weakest precondition")
  }

  @Test
  fun bug4_validLoopInvariant_weakestPreconditionIsNonNull() {
    // A valid invariant yields a non-null weakest precondition.
    val context = Parser().parse(
        """
        vars:
          int x;
        code:
          x := 0;
          while (x < 3) invariant (x >= 0) {
            x := x + 1;
          };
        post: (true)
        """.trimIndent())
    val output = Output()
    output.log = false
    assertTrue(
        WPCProofSystem(context, output).weakestPrecondition(context.post) != null,
        "A valid loop invariant should yield a weakest precondition")
  }

  // -- Fuzz: straight-line scalar programs -----------------------------------
  // Generates deterministic straight-line scalar programs, derives each
  // postcondition from the interpreter, and asserts the WPC proof proves the
  // triple SAFE. Exercises the proof system's handling of scalar arithmetic,
  // aliasing-free assignments, and postcondition matching across many shapes.

  private fun genExpr(random: Random, names: List<String>, depth: Int): String {
    if (depth <= 0 || random.nextBoolean()) {
      return if (random.nextInt(2) == 0) {
        names[random.nextInt(names.size)]
      } else {
        random.nextInt(0, 5).toString()
      }
    }
    val op = listOf("+", "-", "*")[random.nextInt(3)]
    return "(${genExpr(random, names, depth - 1)} $op ${genExpr(random, names, depth - 1)})"
  }

  private fun genProgram(random: Random): Triple<String, String, String> {
    val numVars = random.nextInt(1, 4)
    val names = (0 until numVars).map { "v$it" }
    val numStmts = random.nextInt(3, 8)
    val code = (0 until numStmts).map { _ ->
      val t = names[random.nextInt(numVars)]
      val expr = genExpr(random, names, random.nextInt(0, 3))
      return@map "$t := $expr;"
    }
    val vars = names.joinToString("\n") { "int $it;" }
    return Triple(vars, code.joinToString("\n"), names[random.nextInt(numVars)])
  }

  @Test
  fun fuzz_straightLineScalarPrograms_areSafe() {
    val random = Random(42)
    val failures = mutableListOf<String>()
    repeat(60) { i ->
      val (vars, code, target) = genProgram(random)
      val prog = "vars:\n$vars\ncode:\n$code"
      val observed = interpValue(prog, target)
      val status = proofStatus("$prog\npost: ($target = $observed)")
      if (status != VerificationStatus.SAFE) {
        failures.add("[$i] target=$target observed=$observed status=$status\nvars:\n$vars\ncode:\n$code")
      }
    }
    assertTrue(
        failures.isEmpty(),
        "All straight-line programs should be proven SAFE. Failures:\n" +
            failures.joinToString("\n"))
  }
}
