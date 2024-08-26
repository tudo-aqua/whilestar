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

package tools.aqua.wvm.language

import tools.aqua.wvm.analysis.typesystem.*
import tools.aqua.wvm.machine.Scope

fun <T> expressionType(expression: Expression<T>, type: Type, expected: Type) {
  if (type != expected) {
    throw IllegalArgumentException(
        "Expression $expression should be of type $expected but is of type $type.")
  }
}

fun contextType(ctx: Scope, variable: String, type: Type) {
  if (ctx.type(variable) != type) {
    throw IllegalArgumentException(
        "Variable $variable type $type should agree with context type ${ctx.type(variable)}.")
  }
}

fun proofTreeTermCorrespondence(prf: AddressProofTree, expr: AddressExpression) {
  if (prf.expr != expr) {
    throw IllegalArgumentException("Proof tree $prf should correspond to expression $expr.")
  }
}

fun <T> proofTreeTermCorrespondence(prf: BooleanProofTree, expr: Expression<T>) {
  if (prf.expr != expr) {
    throw IllegalArgumentException("Proof tree $prf should correspond to expression $expr.")
  }
}

fun <T> proofTreeTermCorrespondence(prf: ArithmeticProofTree, expr: Expression<T>) {
  if (prf.expr != expr) {
    throw IllegalArgumentException("Proof tree $prf should correspond to expression $expr.")
  }
}

fun proofTreeTermCorrespondence(prf: StatementProofTree, stmt: Statement) {
  if (prf.stmt != stmt) {
    throw IllegalArgumentException("Proof tree $prf should correspond to statement $stmt.")
  }
}

fun proofTreeTermCorrespondence(prf: SequenceOfStatementsPrf, stmts: SequenceOfStatements) {
  if (prf.stmt != stmts) {
    throw IllegalArgumentException("Proof tree $prf should correspond to statements $stmts.")
  }
}

fun proofTreeTypeCorrespondence(prf: AddressProofTree, type: Type) {
  if (prf.type != type) {
    throw IllegalArgumentException("Proof tree $prf should correspond to type $type.")
  }
}

fun proofTreeTypeCorrespondence(prf: BooleanProofTree, type: Type) {
  if (prf.type != type) {
    throw IllegalArgumentException("Proof tree $prf should correspond to type $type.")
  }
}

fun proofTreeTypeCorrespondence(prf: ArithmeticProofTree, type: Type) {
  if (prf.type != type) {
    throw IllegalArgumentException("Proof tree $prf should correspond to type $type.")
  }
}

fun booleanComparisonNesting(prf: ArithmeticProofTree, nesting: Int) {
  if (prf.type != createNestedPointer(nesting)) {
    throw IllegalArgumentException("Type ${prf.type} should have nesting $nesting.")
  }
}

fun typeEquality(prf1: ExpressionProofTree, prf2: ExpressionProofTree) {
  if (prf1.type != prf2.type) {
    throw IllegalArgumentException("Types ${prf1.type} and ${prf2.type} should be equal.")
  }
}

fun ctxEqual(vararg ctx: Scope) {
  for (ctx1 in ctx) {
    for (ctx2 in ctx) {
      if (!ctx1.typeEqual(ctx2) || !ctx2.typeEqual(ctx1)) {
        throw IllegalArgumentException("Contexts of sub-prooftrees should be equal.")
      }
    }
  }
}

fun statmentType(stmt: Statement, type: Type) {
  if (type != BasicType.UNIT) {
    throw IllegalArgumentException(
        "Expression $stmt should be of type ${BasicType.UNIT} but is of type $type.")
  }
}

fun statmentType(stmts: SequenceOfStatements, type: Type) {
  if (type != BasicType.UNIT) {
    throw IllegalArgumentException(
        "Expression $stmts should be of type ${BasicType.UNIT} but is of type $type.")
  }
}
