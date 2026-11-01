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

package tools.aqua.wvm

import java.math.BigInteger
import java.util.Scanner
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.analysis.hoare.WPCProofSystem
import tools.aqua.wvm.analysis.inductiveVerification.BMCSafetyChecker
import tools.aqua.wvm.analysis.inductiveVerification.KInductionChecker
import tools.aqua.wvm.analysis.semantics.HavocInputErr
import tools.aqua.wvm.analysis.semantics.HavocOk
import tools.aqua.wvm.analysis.semantics.HavocRangeErr
import tools.aqua.wvm.analysis.semantics.NestedStatementError
import tools.aqua.wvm.language.AnyArray
import tools.aqua.wvm.language.ArrayRead
import tools.aqua.wvm.language.Div
import tools.aqua.wvm.language.Eq
import tools.aqua.wvm.language.Not
import tools.aqua.wvm.language.NumericLiteral
import tools.aqua.wvm.language.Rem
import tools.aqua.wvm.language.ValAtAddr
import tools.aqua.wvm.machine.Memory
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

/**
 * Regressions for defects where the original interpreter or proof system contradicted the rest of
 * the tool. Each test fails on the unpatched version.
 */
class BugFixTest {

  private fun parse(source: String) = Parser().parse(source.trimIndent())

  private fun run(vars: String, code: String, input: String? = null) =
      parse(
              """
              vars:
                $vars
              code:
                $code
              """)
          .also { if (input != null) it.input = Scanner(input) }
          .execute(false, Output())

  // --- the interpreter reported a fault but then crashed on the error object ------------------

  @Test
  fun aFaultInAnAssertConditionIsReportedInsteadOfCrashing() {
    val trace = run("int x;", "assert ((1 / 0) = 1);")
    assertTrue(trace.single() is NestedStatementError)
    assertTrue(trace.single().result.dst.error)
  }

  @Test
  fun aFaultInAnIfConditionIsReportedInsteadOfCrashing() {
    val trace = run("int x;", "if ((1 / 0) = 1) { x := 1; } else { x := 2; };")
    assertTrue(trace.single() is NestedStatementError)
    assertTrue(trace.single().result.dst.error)
  }

  @Test
  fun aFaultInAWhileConditionIsReportedInsteadOfCrashing() {
    val trace = run("int x;", "while ((1 / 0) = 1) { x := 1; };")
    val err = trace.single() as NestedStatementError
    assertTrue(err.result.dst.error)
    assertEquals("WhileErr", err.ruleName)
  }

  // --- extern accepted an input outside the declared range ------------------------------------

  @Test
  fun externAcceptsItsDeclaredUpperBoundButNothingAboveIt() {
    assertTrue(run("int x;", "extern x 1 .. 10;", "10").single() is HavocOk)
    assertTrue(run("int x;", "extern x 1 .. 10;", "9").single() is HavocOk)
    assertTrue(run("int x;", "extern x 1 .. 10;", "11").single() is HavocRangeErr)
    assertTrue(run("int x;", "extern x 1 .. 10;", "0").single() is HavocRangeErr)
  }

  @Test
  fun emptyExternInputIsReportedAsALanguageError() {
    val trace = run("int x;", "extern x 0 .. 5;", "")
    assertTrue(trace.single() is HavocInputErr)
    assertTrue(trace.single().result.dst.error)
  }

  @Test
  fun nonNumericExternInputIsReportedAsALanguageError() {
    val trace = run("int x;", "extern x 0 .. 5;", "not-a-number")
    assertTrue(trace.single() is HavocInputErr)
    assertTrue(trace.single().result.dst.error)
  }

  @Test
  fun externDrawsFromTheWholeDeclaredRange() {
    val upper = BigInteger("99999999999999999999")
    val scope = parse("vars:\n  int x;\ncode:\n").scope
    val havoc =
        tools.aqua.wvm.language.Havoc(tools.aqua.wvm.language.Variable("x"), BigInteger.ZERO, upper)
    val samples =
        (1..200).map {
          (havoc
              .execute(
                  tools.aqua.wvm.machine.Configuration(
                      tools.aqua.wvm.language.SequenceOfStatements(listOf(havoc)),
                      scope,
                      Memory(Array(1) { BigInteger.ZERO })),
                  null)
              .result
              .dst
              .memory
              .read(0))
        }
    assertTrue(samples.all { it >= BigInteger.ZERO && it < upper }, "$samples")
    assertTrue(samples.any { it > BigInteger.valueOf(Long.MAX_VALUE) }, "range was truncated")
  }

  // --- parser error message on a file without a trailing newline ------------------------------

  @Test
  fun aParseErrorInTheLastLineIsReported() {
    val error =
        assertThrows(Exception::class.java) { Parser().parse("vars:\n  int x;\ncode:\n  x := ;") }
    assertTrue(error.message!!.contains("while parsing"), error.message)
    assertFalse(error.message!!.contains("out of bounds"), error.message)
  }

  // --- Memory accepted one address behind the last cell ---------------------------------------

  @Test
  fun memoryRejectsTheAddressBehindTheLastCell() {
    val memory = Memory(Array(2) { BigInteger.ZERO })
    val read = assertThrows(Exception::class.java) { memory.read(2) }
    assertTrue(read.message!!.contains("segmentation fault"), read.message)
    val write = assertThrows(Exception::class.java) { memory.write(2, BigInteger.ONE) }
    assertTrue(write.message!!.contains("segmentation fault"), write.message)
    assertEquals(BigInteger.ZERO, memory.read(1))
  }

  // --- the proof system used floor division while the interpreter truncates -------------------

  @Test
  fun divisionEncodingMatchesTheInterpreterForEverySign() {
    for ((dividend, divisor) in
        listOf(5 to 3, -5 to 3, 5 to -3, -5 to -3, 6 to 3, -6 to 3, 1 to -2, -5 to 2, -5 to 1)) {
      val left = BigInteger.valueOf(dividend.toLong())
      val right = BigInteger.valueOf(divisor.toLong())
      expectEncoded(Div(NumericLiteral(left), NumericLiteral(right)), left.divide(right))
      expectEncoded(Rem(NumericLiteral(left), NumericLiteral(right)), left.remainder(right))
    }
  }

  private fun expectEncoded(
      expr: tools.aqua.wvm.language.ArithmeticExpression,
      expected: BigInteger
  ) {
    val mismatch = SMTSolver().solve(Not(Eq(expr, NumericLiteral(expected), 0)))
    assertEquals(SatStatus.UNSAT, mismatch.status, "$expr is not $expected")
  }

  // --- the proof system left array indices unsubstituted --------------------------------------

  @Test
  fun substitutionReachesIntoAnArrayIndex() {
    val system =
        proof(
            """
            vars:
              int i;
              int[3] a;
            pre: (true)
            code:
              i := 1;
              a[0] := 5;
            post: (a[i] = 0)
            """)
    // a[1] is untouched; a prover that leaves i unsubstituted reads a[0], which is 5
    assertTrue(system.proof())
  }

  @Test
  fun varAddressIsAcceptedByTheProofSystemLikeKInduction() {
    val context =
        parse(
            """
            vars:
              int x;
              int *y;
            pre: (true)
            code:
              x := 10;
              y := &x;
              *y := 11;
            post: (x = 11)
            """)
    assertTrue(
        WPCProofSystem(context, Output()).proof(), "WPC should prove the pointer program safe")
    assertTrue(
        KInductionChecker(context).check(), "k-induction should prove the pointer program safe")
  }

  private fun proof(source: String) = WPCProofSystem(parse(source), Output())

  // --- the initial memory of the proof system did not match the interpreter -------------------

  @Test
  fun theInitialMemoryUsesTheDeclaredAddresses() {
    val context = parse("vars:\n  int[2] b;\n  int a;\ncode:\n  a := 0;\n")
    val pre = WPCProofSystem(context, Output()).augment(context.pre, context.scope)
    // the interpreter lays out b at 0 (two cells) and a at 3
    assertEquals(3, context.scope.resolve("a"))
    assertTrue(pre.toString().contains("(b = M[0])"), pre.toString())
    assertTrue(pre.toString().contains("(a = M[3])"), pre.toString())

    val ts = tools.aqua.wvm.analysis.inductiveVerification.TransitionSystem(context)
    assertTrue(ts.initial.toString().contains("(b = 0)"), ts.initial.toString())
    assertTrue(ts.initial.toString().contains("(a = 3)"), ts.initial.toString())
  }

  @Test
  fun theModelCheckerUsesTheDeclaredAddresses() {
    // b is the array and its cell holds the pointer to the data (address + 1), a is 0. Nothing
    // changes, so `b = 1` holds. With the initial state taken from the symbol map the checkers
    // read a different cell and reported the program as unsafe.
    val context =
        parse(
            """
            vars:
              int[2] b;
              int a;
            pre: (true)
            code:
            post: (b = 1)
            """)
    assertTrue(KInductionChecker(context).check(), "k-induction should prove the program safe")
    assertFalse(BMCSafetyChecker(context).check(), "BMC should not find a counterexample")
  }

  // --- the proof system crashed with a third extern statement ---------------------------------

  @Test
  fun severalExternStatementsDoNotCrashTheProver() {
    val system =
        proof(
            """
            vars:
              int x;
              int y;
              int z;
            pre: (true)
            code:
              extern x 0 .. 5;
              extern y 0 .. 5;
              extern z 0 .. 5;
            post: (true)
            """)
    assertTrue(system.proof())
  }

  // --- a model with a constant array made the proof system fail --------------------------------

  @Test
  fun aSatisfiableQueryReturnsItsStatusInsteadOfFailing() {
    // the query uses the memory, so Z3 returns it as a constant array, which konstraints cannot
    // turn into a model
    val expr = Eq(ValAtAddr(ArrayRead(AnyArray, lit(0))), lit(1), 0)
    SMTSolver.resetCallCounters()
    val result = SMTSolver().solve(expr)
    assertEquals(SatStatus.SAT, result.status)
    assertFalse(result.modelAvailable)
    // the model could not be read, so the query was posed once more without one
    assertEquals(2, SMTSolver.numberOfSMTCalls)
    SMTSolver.resetCallCounters()
  }

  @Test
  fun aSatisfiableQueryWithoutMemoryKeepsItsModel() {
    // the memory is only declared when a query uses it, so a query without it can still print
    // the model instead of falling back to a query without one
    val result = SMTSolver().solve(Not(Eq(lit(1), lit(2), 0)))
    assertEquals(SatStatus.SAT, result.status)
    assertTrue(result.modelAvailable)
  }

  private fun lit(value: Int): NumericLiteral = NumericLiteral(BigInteger.valueOf(value.toLong()))
}
