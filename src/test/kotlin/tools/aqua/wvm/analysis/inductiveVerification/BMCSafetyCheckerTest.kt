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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import tools.aqua.wvm.analysis.VerificationStatus
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

/**
 * Regression tests for the transition-system memory layout of `&x` (VarAddress).
 *
 * The TS encodes a variable `x` as an SMT constant holding its *static address*, and the value of
 * `x` is read from the memory array as `M[x]`. `&x` therefore must resolve to the *static address
 * constant* of `x` (which [TransitionSystem.initMemory] pins to the WVM runtime address
 * `Scope.resolve(x)`, i.e. declaration order), NOT to a value and NOT to an address derived from a
 * local counter over the non-deterministic `HashMap` symbol order.
 */
class BMCSafetyCheckerTest {

  private fun check(source: String): VerificationStatus {
    val context: Context = Parser().parse(source)
    val output = Output()
    output.log = false
    return BMCSafetyChecker(context, output, maxBound = 5).check().status
  }

  private fun parse(source: String): Context = Parser().parse(source.trimIndent())

  // Canonical example from the task: p := &a; *p := 5 must write to a, so a = 5 at the end.
  // The postcondition holds, hence BMC must find no counterexample.
  @Test
  fun dereferenceThroughAddressOfPointerIsSound() {
    assertEquals(
        VerificationStatus.UNKNOWN,
        check(
            """
            vars:
              int a;
              int *p;
            code:
              p := &a;
              *p := 5;
            post: (a = 5)
            """
                .trimIndent()))
  }

  // a is the first variable, so the runtime address of a is 0. The postcondition p = 0 holds,
  // hence BMC must find no counterexample.
  // Regression: with a local counter over the HashMap (which iterates `p, a` for these names),
  // the address of `a` was pinned to 1, so p became 1 and this true postcondition was
  // incorrectly refuted.
  @Test
  fun addressOfFirstVariableIsZero() {
    assertEquals(
        VerificationStatus.UNKNOWN,
        check(
            """
            vars:
              int a;
              int *p;
            code:
              p := &a;
            post: (p = 0)
            """
                .trimIndent()))
  }

  // Soundness: p must NOT become the value of a (5). Since a = 5 and p = addr(a) = 0, the
  // postcondition p = 5 is false, hence BMC must refute it.
  @Test
  fun addressOfIsNotTheValueOfTheVariable() {
    assertEquals(
        VerificationStatus.UNSAFE,
        check(
            """
            vars:
              int a;
              int *p;
            code:
              a := 5;
              p := &a;
            post: (p = 5)
            """
                .trimIndent()))
  }

  // Direct permutation regression: at runtime addr(a) = 0, so p = 0 and the postcondition
  // p = 1 is false, hence BMC must refute it.
  // Regression: with the HashMap-based counter the address of `a` was permuted to 1, making p = 1
  // and (unsoundly) proving this false postcondition.
  @Test
  fun addressOfPointerIsNotPermutedToAnotherVariable() {
    assertEquals(
        VerificationStatus.UNSAFE,
        check(
            """
            vars:
              int a;
              int *p;
            code:
              p := &a;
            post: (p = 1)
            """
                .trimIndent()))
  }

  @Test
  fun bmcReportsUnknownWhenTheBoundHasNoCounterexample() {
    val context =
        parse(
            """
        vars:
          int x;
        code:
          x := 1;
        post: (x = 1)
        """)
    assertEquals(
        VerificationStatus.UNKNOWN,
        BMCSafetyChecker(context, Output(), maxBound = 0).check().status)
  }

  @Test
  fun bmcReportsUnsafeForAReachableViolation() {
    val context =
        parse(
            """
        vars:
          int x;
        code:
          x := 1;
        post: (x = 0)
        """)
    assertEquals(
        VerificationStatus.UNSAFE, BMCSafetyChecker(context, Output(), maxBound = 5).check().status)
  }

  @Test
  fun kInductionReportsUnsafeForAReachableViolation() {
    val context =
        parse(
            """
        vars:
          int x;
        code:
          x := 1;
        post: (x = 0)
        """)
    assertEquals(
        VerificationStatus.UNSAFE, KInductionChecker(context, Output(), kBound = 5).check().status)
  }

  @Test
  fun kInductionReportsUnknownWhenTheBoundIsZero() {
    val context =
        parse(
            """
        vars:
          int x;
        code:
          x := 1;
        post: (x = 1)
        """)
    assertEquals(
        VerificationStatus.UNKNOWN, KInductionChecker(context, Output(), kBound = 0).check().status)
  }

  @Test
  fun combinedCheckerReportsUnknownWhenTheBoundIsZero() {
    val context =
        parse(
            """
        vars:
          int x;
        code:
          x := 1;
        post: (x = 1)
        """)
    assertEquals(
        VerificationStatus.UNKNOWN,
        KInductionCheckerWithBMC(context, Output(), kBound = 0).check().status)
  }

  @Test
  fun combinedCheckerReportsUnsafeForAReachableViolation() {
    val context =
        parse(
            """
        vars:
          int x;
        code:
          x := 1;
        post: (x = 0)
        """)
    assertEquals(
        VerificationStatus.UNSAFE,
        KInductionCheckerWithBMC(context, Output(), kBound = 5).check().status)
  }

  @Test
  fun combinedCheckerReportsSafeAfterAnInductiveProof() {
    val context =
        parse(
            """
        vars:
          int x;
        code:
          x := 1;
        post: (x = 1)
        """)
    assertEquals(
        VerificationStatus.SAFE,
        KInductionCheckerWithBMC(context, Output(), kBound = 5).check().status)
  }
}
