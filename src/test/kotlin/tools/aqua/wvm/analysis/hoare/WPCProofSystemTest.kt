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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tools.aqua.wvm.analysis.VerificationStatus
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

class WPCProofSystemTest {

  private fun proof(source: String): Boolean = proofStatus(source) == VerificationStatus.SAFE

  private fun proofResult(source: String): tools.aqua.wvm.analysis.VerificationResult {
    val context: Context = Parser().parse(source)
    val output = Output()
    output.log = false
    return WPCProofSystem(context, output).proof()
  }

  private fun proofStatus(source: String): VerificationStatus = proofResult(source).status

  @Test
  fun scalarAssignmentProvable() {
    assertTrue(
        proof(
            """
            vars:
              int x;
            code:
              x := 7;
            post: (x = 7)
            """
                .trimIndent()))
  }

  @Test
  fun unresolvedAddressIsReportedUnknown() {
    assertEquals(
        VerificationStatus.UNKNOWN,
        proofStatus(
            """
            vars:
              int x;
            code:
              x := &missing;
            post: (x = 0)
            """
                .trimIndent()))
  }

  @Test
  fun proofTableEntryPointRemainsCompatibleWithWiz() {
    val context =
        Parser()
            .parse(
                """
            vars:
              int x;
            code:
              x := 1;
            post: (x = 1)
            """
                    .trimIndent())
    val proofTable = mutableListOf<ProofTableRow>()

    assertTrue(WPCProofSystem(context, Output()).proof(proofTable))
    assertTrue(proofTable.isNotEmpty())
  }

  @Test
  fun scalarAssignmentFalsifiable() {
    assertFalse(
        proof(
            """
            vars:
              int x;
            code:
              x := 1;
            post: (x = 2)
            """
                .trimIndent()))
  }

  @Test
  fun falsePostconditionIsReportedUnsafe() {
    assertEquals(
        VerificationStatus.UNSAFE,
        proofStatus(
            """
            vars:
              int x;
            code:
              x := 1;
            post: (x = 2)
            """
                .trimIndent()))
  }

  @Test
  fun arrayCounterexampleIncludesRawZ3Model() {
    val result =
        proofResult(
            """
            vars:
              int* x;
              int[3] y;
              int z;
            pre: (true)
            code:
              y[1] := y[0] + y[2];
              y[0] := 1;
              y[1] := 2;
              y[2] := 7;
              x := y;
              print "x[1] = y[1] = ", x[2];
            post: (x[2] = 2)
            """
                .trimIndent())
    assertEquals(VerificationStatus.UNSAFE, result.status)
    assertTrue(result.details?.contains("M_") == true, result.toString())
    assertFalse(result.details?.contains("model not representable") == true, result.toString())
  }

  @Test
  fun proofTableCounterexampleIncludesRawZ3Model() {
    val context =
        Parser()
            .parse(
                """
                vars:
                  int* x;
                  int[3] y;
                  int z;
                pre: (true)
                code:
                  y[1] := y[0] + y[2];
                  y[0] := 1;
                  y[1] := 2;
                  y[2] := 7;
                  x := y;
                  print "x[1] = y[1] = ", x[2];
                post: (x[2] = 2)
                """
                    .trimIndent())
    val proofTable = mutableListOf<ProofTableRow>()

    assertFalse(WPCProofSystem(context, Output()).proof(proofTable))
    assertTrue(
        proofTable.flatMap { it.vcs }.any { it.result.contains("M_") },
        proofTable.flatMap { it.vcs }.joinToString("\n") { it.result })
  }

  // Soundness: the postcondition x[2] = 1 is NOT implied by the program
  // (x[2] is y[2] = 7 after x := y). Before the fix, x kept its (initial) value 0 in the
  // postcondition, and the store y[0] := 1 landed on address y + 0 = 2, making M[0 + 2] = 1
  // (wrongly) provable.
  @Test
  fun pointerCopyFalsifiesFalsePostcondition() {
    assertFalse(
        proof(
            """
            vars:
              int* x;
              int[3] y;
            code:
              y[0] := 1;
              y[2] := 7;
              x := y;
            post: (x[2] = 1)
            """
                .trimIndent()))
  }

  // Completeness: x := y copies the pointer, so x[2] = y[2] = 7. Before the fix, x was not
  // substituted at all inside the postcondition, so the correct postcondition could not be
  // proved.
  @Test
  fun pointerCopyProvesTruePostcondition() {
    assertTrue(
        proof(
            """
            vars:
              int* x;
              int[3] y;
            code:
              y[2] := 7;
              x := y;
            post: (x[2] = 7)
            """
                .trimIndent()))
  }

  // The dereference of a copied pointer must reflect the copied base address:
  // z := *x after x := y reads y[0].
  @Test
  fun dereferenceOfPointerCopy() {
    assertTrue(
        proof(
            """
            vars:
              int* x;
              int[3] y;
              int z;
            code:
              y[0] := 9;
              x := y;
              z := *x;
            post: (z = 9)
            """
                .trimIndent()))
  }

  // Array base address: the address of a[2] after a[0] := 1 must still be 2.
  @Test
  fun arrayBaseAddressPreserved() {
    assertTrue(
        proof(
            """
            vars:
              int[3] a;
              int z;
            code:
              a[0] := 1;
              z := a[2];
            post: (z = 0)
            """
                .trimIndent()))
  }

  // &x evaluates to the static memory address of x (a compile-time constant), not to the
  // value of x. a is the first variable, so addr(a) = 0.
  @Test
  fun addressOfFirstVariableIsZero() {
    assertTrue(
        proof(
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

  // Soundness regression: &a must NOT be translated to the value of a. With a := 5 the
  // (unsound) translation &a -> a would make p = 5 and wrongly prove this postcondition;
  // at runtime p = addr(a) = 0, so the postcondition is false and the proof must fail.
  @Test
  fun addressOfIsNotTheValueOfTheVariable() {
    assertFalse(
        proof(
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

  // Two distinct variables have distinct static addresses: addr(p) = 1 here.
  @Test
  fun addressOfSecondVariableIsOne() {
    assertTrue(
        proof(
            """
            vars:
              int a;
              int *p;
            code:
              p := &p;
            post: (p = 1)
            """
                .trimIndent()))
  }

  // Regression for the memory-model soundness of scalar reads written through a pointer.
  // `p := &a` makes p = addr(a); `*p := 5` writes 5 to the cell holding a. The postcondition
  // a = 5 MUST be provable. Before the fix the store into memory did not propagate to the
  // scalar read of `a` (a bare SMT constant in the WPC), so the proof wrongly failed.
  @Test
  fun dereferenceWriteThroughAddressOfPointerIsSound() {
    assertTrue(
        proof(
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

  // The negation of the above: writing a wrong value through the pointer must NOT make the
  // postcondition hold. `*p := 5` leaves a = 5, so a = 6 must be refuted.
  @Test
  fun dereferenceWriteThroughAddressOfPointerFalsifies() {
    assertFalse(
        proof(
            """
            vars:
              int a;
              int *p;
            code:
              p := &a;
              *p := 5;
            post: (a = 6)
            """
                .trimIndent()))
  }
}
