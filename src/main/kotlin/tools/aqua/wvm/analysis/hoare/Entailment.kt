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

import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.wvm.language.And
import tools.aqua.wvm.language.BooleanExpression
import tools.aqua.wvm.language.Not

data class Entailment(
    val left: BooleanExpression,
    val right: BooleanExpression,
    val explanation: String,
    val leftDisplay: String? = null,
    val rightDisplay: String? = null
) {

  override fun toString(): String = "$explanation: (⊧ $left $right)"

  fun smtTest() = And(left, Not(right))
}

data class VerificationCondition(val entailment: Entailment, var result: String = "not solved") {
  val explanation: String
    get() = entailment.explanation

  val implication: String
    get() =
        "(${entailment.leftDisplay ?: entailment.left} ⊧ ${entailment.rightDisplay ?: entailment.right})"

  fun solve(): SatStatus {
    val solver = SMTSolver()
    val smtResult = solver.solve(entailment.smtTest())
    result =
        when (smtResult.status) {
          SatStatus.UNSAT -> "successful."
          SatStatus.SAT -> "counterexample: ${smtResult.model}"
          SatStatus.UNKNOWN -> "could not be decided.."
          SatStatus.PENDING -> "error during solving."
        }
    return smtResult.status
  }
}

data class ProofTableRow(
    val statement: String,
    var wpc: String,
    var post: String,
    var vcs: MutableList<VerificationCondition> = mutableListOf(),
    var commentWPC: String? = null,
    val commentPost: String? = null
)
