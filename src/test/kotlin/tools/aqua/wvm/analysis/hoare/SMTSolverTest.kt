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

import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.wvm.language.Add
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.AnyArray
import tools.aqua.wvm.language.ArrayExpression
import tools.aqua.wvm.language.ArrayRead
import tools.aqua.wvm.language.ArrayWrite
import tools.aqua.wvm.language.Eq
import tools.aqua.wvm.language.Lte
import tools.aqua.wvm.language.Not
import tools.aqua.wvm.language.NumericLiteral
import tools.aqua.wvm.language.True
import tools.aqua.wvm.language.ValAtAddr
import tools.aqua.wvm.language.Variable

// Safety-net tests for SMTSolver.solve: the solver must never crash on the failed-proof (SAT)
// scenarios of the verification conditions. The model values are only used for display by the
// callers, so the correct status is the contract asserted here.
class SMTSolverTest {

  // M[base + offset] as it appears in prepared WPCs (memory read at address base + offset).
  private fun memRead(base: String, offset: BigInteger) =
      ValAtAddr(ArrayRead(AnyArray, Add(ValAtAddr(Variable(base)), NumericLiteral(offset))))

  // M_<base + offset <| value> as introduced by the WPC for assignments.
  private fun memWrite(base: String, offset: BigInteger, value: BigInteger): ArrayExpression =
      ArrayWrite(
          AnyArray, Add(ValAtAddr(Variable(base)), NumericLiteral(offset)), NumericLiteral(value))

  // x + 1 = 3: SAT. The model must interpret x. The lazily declared memory array must not be
  // part of the model, because no array expression occurs in the condition (with an
  // unconditional M_ declaration the model extraction crashed on this exact shape).
  @Test
  fun scalarSatProducesModelWithoutMemoryArray() {
    val result =
        SMTSolver()
            .solve(
                Eq(
                    Add(ValAtAddr(Variable("x")), NumericLiteral(BigInteger.ONE)),
                    NumericLiteral(BigInteger.valueOf(3)),
                    0))
    assertEquals(SatStatus.SAT, result.status)
    assertTrue(result.model.containsKey("x"))
    assertFalse(result.model.containsKey("M_"))
  }

  // x + 1 = 3 and x <= 0: UNSAT.
  @Test
  fun scalarUnsat() {
    val result =
        SMTSolver()
            .solve(
                And(
                    Eq(
                        Add(ValAtAddr(Variable("x")), NumericLiteral(BigInteger.ONE)),
                        NumericLiteral(BigInteger.valueOf(3)),
                        0),
                    Lte(ValAtAddr(Variable("x")), NumericLiteral(BigInteger.ZERO))))
    assertEquals(SatStatus.UNSAT, result.status)
  }

  // M[1] = 1 and M[1] = 2: UNSAT with a declared memory array.
  @Test
  fun arrayUnsat() {
    val result =
        SMTSolver()
            .solve(
                And(
                    Eq(
                        ValAtAddr(ArrayRead(AnyArray, NumericLiteral(BigInteger.ONE))),
                        NumericLiteral(BigInteger.ONE),
                        0),
                    Eq(
                        ValAtAddr(ArrayRead(AnyArray, NumericLiteral(BigInteger.ONE))),
                        NumericLiteral(BigInteger.valueOf(2)),
                        0)))
    assertEquals(SatStatus.UNSAT, result.status)
  }

  // The crashed end-to-end case: the store chain M_<y + 2 <| 7><y + 0 <| 1> whose model Z3
  // represents as a constant array ((as const (Array Int Int)) 0). konstraints-z3 cannot convert
  // that model; solve() must still report SAT and mark the model unavailable.
  @Test
  fun constArrayStoreChainDoesNotCrash() {
    val chain =
        ArrayWrite(
            memWrite("y", BigInteger.valueOf(2), BigInteger.valueOf(7)),
            Add(ValAtAddr(Variable("y")), NumericLiteral(BigInteger.ZERO)),
            NumericLiteral(BigInteger.ONE))
    val vc =
        And(
            True,
            Not(
                Eq(
                    ValAtAddr(
                        ArrayRead(
                            chain,
                            Add(ValAtAddr(Variable("x")), NumericLiteral(BigInteger.valueOf(2))))),
                    NumericLiteral(BigInteger.valueOf(1)),
                    0)))
    val result = SMTSolver().solve(vc)
    assertEquals(SatStatus.SAT, result.status)
    assertFalse(result.modelAvailable)
    assertTrue(result.modelText().contains("M_"), result.modelText())
    assertFalse(result.modelText().contains("model not representable"), result.modelText())
  }
}
