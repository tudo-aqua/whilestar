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

package tools.aqua.wvm.analysis.typesystem

import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Scope

interface ProofTree {
  fun print(indent: String)
}

// Expression Proof Trees
abstract class ExpressionProofTree(open val type: Type) : ProofTree

open class BooleanProofTree(
    val ctx: Scope,
    val expr: BooleanExpression,
    override val type: Type,
    val desc: String,
    vararg val children: ExpressionProofTree
) : ExpressionProofTree(type) {

  override fun print(indent: String) {
    println("$indent$desc")
    children.forEach { it.print("$indent  ") }
  }
}

open class AddressProofTree(
    val ctx: Scope,
    val expr: AddressExpression,
    override val type: Type,
    val desc: String,
    vararg val children: ExpressionProofTree
) : ExpressionProofTree(type) {
  override fun print(indent: String) {
    println("$indent$desc")
    children.forEach { it.print("$indent  ") }
  }
}

open class ArithmeticProofTree(
    val ctx: Scope,
    val expr: ArithmeticExpression,
    override val type: Type,
    val desc: String,
    vararg val children: ExpressionProofTree
) : ExpressionProofTree(type) {

  override fun print(indent: String) {
    println("$indent$desc")
    children.forEach { it.print("$indent  ") }
  }
}

// Proof Tree Node for Literals
class NumericLiteralPrf(ctx: Scope, literal: NumericLiteral, type: Type) :
    ArithmeticProofTree(ctx, literal, type, "Literal: $literal -> $type") {

  init {
    expressionType(literal, type, BasicType.INT)
  }
}

class TruePrf(ctx: Scope, literal: True, type: Type) :
    BooleanProofTree(ctx, literal, type, "Literal: $literal -> $type") {

  init {
    expressionType(literal, type, BasicType.BOOLEAN)
  }
}

class FalsePrf(ctx: Scope, literal: False, type: Type) :
    BooleanProofTree(ctx, literal, type, "Literal: $literal -> $type") {

  init {
    expressionType(literal, type, BasicType.BOOLEAN)
  }
}

// Proof Tree Nodes for Memory Access
class VarPrf(ctx: Scope, variable: String, type: Type) :
    AddressProofTree(ctx, Variable(variable), type, "Variable: $variable -> $type") {

  init {
    contextType(ctx, variable, type)
  }
}

class DeRefPrf(ctx: Scope, expr: DeRef, type: Type, child: AddressProofTree) :
    AddressProofTree(ctx, expr, type, "De-reference: $expr -> $type", child) {

  init {
    proofTreeTermCorrespondence(child, expr.reference)
    proofTreeTypeCorrespondence(child, Pointer(type))
    ctxEqual(ctx, child.ctx)
  }
}

class RefPrf(ctx: Scope, expr: VarAddress, type: Type, child: AddressProofTree) :
    ArithmeticProofTree(ctx, expr, type, "Reference: $expr -> $type", child) {

  init {
    proofTreeTermCorrespondence(child, expr.variable)
    proofTreeTypeCorrespondence(child, unreferenceType(type))
    ctxEqual(ctx, child.ctx)
  }
}

class ValAtAddrPrf(ctx: Scope, expr: ValAtAddr, type: Type, child: AddressProofTree) :
    ArithmeticProofTree(ctx, expr, type, "Value at Addr: $expr -> $type", child) {

  init {
    proofTreeTermCorrespondence(child, expr.addr)
    proofTreeTypeCorrespondence(child, type)
    ctxEqual(ctx, child.ctx)
  }
}

class ArrayAccessPrf(
    ctx: Scope,
    expr: ArrayAccess,
    type: Type,
    arrayChild: ValAtAddrPrf,
    indexChild: ArithmeticProofTree
) : AddressProofTree(ctx, expr, type, "Array Access: $expr -> $type", arrayChild, indexChild) {

  init {
    proofTreeTermCorrespondence(arrayChild, expr.array)
    proofTreeTermCorrespondence(indexChild, expr.index)
    proofTreeTypeCorrespondence(arrayChild, Pointer(type))
    expressionType(expr.index, indexChild.type, BasicType.INT)
    ctxEqual(arrayChild.ctx, indexChild.ctx, ctx)
  }
}

// Proof Tree Nodes for Arithmetic Operations
class AdditionPrf(
    ctx: Scope,
    expr: Add,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : ArithmeticProofTree(ctx, expr, type, "Addition: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.INT)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class SubtractionPrf(
    ctx: Scope,
    expr: Sub,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : ArithmeticProofTree(ctx, expr, type, "Subtraction: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.INT)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class MultiplicationPrf(
    ctx: Scope,
    expr: Mul,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : ArithmeticProofTree(ctx, expr, type, "Multiplication: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.INT)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class DivisionPrf(
    ctx: Scope,
    expr: Div,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : ArithmeticProofTree(ctx, expr, type, "Division: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.INT)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class RemainderPrf(
    ctx: Scope,
    expr: Rem,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : ArithmeticProofTree(ctx, expr, type, "Remainder: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.INT)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class UnaryMinusPrf(ctx: Scope, expr: UnaryMinus, type: Type, child: ArithmeticProofTree) :
    ArithmeticProofTree(ctx, expr, type, "Unary Minus: $expr -> $type", child) {

  init {
    expressionType(expr, type, BasicType.INT)
    proofTreeTermCorrespondence(child, expr.negated)
    expressionType(expr.negated, child.type, BasicType.INT)
    ctxEqual(child.ctx, ctx)
  }
}

// Proof Tree Nodes for Boolean Operations
class EqualityPrf(
    ctx: Scope,
    expr: Eq,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : BooleanProofTree(ctx, expr, type, "Equality: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    // expressionType(expr.left, lhs.type, BasicType.INT)
    // expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
    typeEquality(lhs, rhs)
    booleanComparisonNesting(lhs, expr.nesting)
    booleanComparisonNesting(rhs, expr.nesting)
  }
}

class GreaterThanPrf(
    ctx: Scope,
    expr: Gt,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : BooleanProofTree(ctx, expr, type, "Greater Than: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class GreaterThanOrEqualPrf(
    ctx: Scope,
    expr: Gte,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : BooleanProofTree(ctx, expr, type, "Greater Than Or Equal: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class LessThanPrf(
    ctx: Scope,
    expr: Lt,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : BooleanProofTree(ctx, expr, type, "Less Than: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class LessThanOrEqualPrf(
    ctx: Scope,
    expr: Lte,
    type: Type,
    lhs: ArithmeticProofTree,
    rhs: ArithmeticProofTree
) : BooleanProofTree(ctx, expr, type, "Less Than Or Equal: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    expressionType(expr.left, lhs.type, BasicType.INT)
    expressionType(expr.right, rhs.type, BasicType.INT)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class NegatePrf(ctx: Scope, expr: Not, type: Type, child: BooleanProofTree) :
    BooleanProofTree(ctx, expr, type, "Negate: $expr -> $type", child) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(child, expr.negated)
    proofTreeTypeCorrespondence(child, BasicType.BOOLEAN)
    ctxEqual(ctx, child.ctx)
  }
}

class AndPrf(ctx: Scope, expr: And, type: Type, lhs: BooleanProofTree, rhs: BooleanProofTree) :
    BooleanProofTree(ctx, expr, type, "And: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    proofTreeTypeCorrespondence(lhs, BasicType.BOOLEAN)
    proofTreeTypeCorrespondence(rhs, BasicType.BOOLEAN)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class OrPrf(ctx: Scope, expr: Or, type: Type, lhs: BooleanProofTree, rhs: BooleanProofTree) :
    BooleanProofTree(ctx, expr, type, "Or: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    proofTreeTypeCorrespondence(lhs, BasicType.BOOLEAN)
    proofTreeTypeCorrespondence(rhs, BasicType.BOOLEAN)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class ImplyPrf(ctx: Scope, expr: Imply, type: Type, lhs: BooleanProofTree, rhs: BooleanProofTree) :
    BooleanProofTree(ctx, expr, type, "Imply: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    proofTreeTypeCorrespondence(lhs, BasicType.BOOLEAN)
    proofTreeTypeCorrespondence(rhs, BasicType.BOOLEAN)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class EquivPrf(ctx: Scope, expr: Equiv, type: Type, lhs: BooleanProofTree, rhs: BooleanProofTree) :
    BooleanProofTree(ctx, expr, type, "Equivalence: $expr -> $type", lhs, rhs) {

  init {
    expressionType(expr, type, BasicType.BOOLEAN)
    proofTreeTermCorrespondence(lhs, expr.left)
    proofTreeTermCorrespondence(rhs, expr.right)
    proofTreeTypeCorrespondence(lhs, BasicType.BOOLEAN)
    proofTreeTypeCorrespondence(rhs, BasicType.BOOLEAN)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

// Statement Proof Trees
open class StatementProofTree(
    val ctx: Scope,
    val stmt: Statement,
    val type: Type,
    val desc: String,
    vararg val children: ProofTree
) : ProofTree {

  override fun print(indent: String) {
    println("$indent$desc")
    children.forEach { it.print("$indent  ") }
  }
}

class AssignmentPrf(
    ctx: Scope,
    stmt: Assignment,
    type: Type,
    val lhs: AddressProofTree,
    val rhs: ArithmeticProofTree
) : StatementProofTree(ctx, stmt, type, "Assignment: $stmt -> $type", lhs, rhs) {

  init {
    statmentType(stmt, type)
    proofTreeTermCorrespondence(lhs, stmt.addr)
    proofTreeTermCorrespondence(rhs, stmt.expr)
    typeEquality(lhs, rhs)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class HavocPrf(ctx: Scope, stmt: Havoc, type: Type, val addrPrf: AddressProofTree) :
    StatementProofTree(ctx, stmt, type, "Havoc: $stmt -> $type", addrPrf) {

  init {
    statmentType(stmt, type)
    proofTreeTermCorrespondence(addrPrf, stmt.addr)
    proofTreeTypeCorrespondence(addrPrf, BasicType.INT)
    ctxEqual(ctx, addrPrf.ctx)
  }
}

class SwapPrf(
    ctx: Scope,
    stmt: Swap,
    type: Type,
    val lhs: AddressProofTree,
    val rhs: AddressProofTree
) : StatementProofTree(ctx, stmt, type, "Swap: $stmt -> $type", lhs, rhs) {

  init {
    statmentType(stmt, type)
    proofTreeTermCorrespondence(lhs, stmt.left)
    proofTreeTermCorrespondence(rhs, stmt.right)
    typeEquality(lhs, rhs)
    ctxEqual(ctx, lhs.ctx, rhs.ctx)
  }
}

class AssertPrf(
    ctx: Scope,
    stmt: Assertion,
    type: Type,
    val condPrf: BooleanProofTree,
) : StatementProofTree(ctx, stmt, type, "Assert; $stmt -> $type", condPrf) {

  init {
    statmentType(stmt, type)
    proofTreeTermCorrespondence(condPrf, stmt.cond)
    ctxEqual(ctx, condPrf.ctx)
  }

  override fun print(indent: String) {
    println("$indent$desc")
    children.forEach { it.print("$indent  ") }
  }
}


class SequenceOfStatementsPrf(
    val ctx: Scope,
    val stmt: SequenceOfStatements,
    val type: Type,
    val prfs: List<StatementProofTree>
) {

  fun print(indent: String) {
    println("${indent}List of Statements -> $type")
    prfs.forEach { it.print("$indent  ") }
  }

  init {
    statmentType(stmt, type)

    for ((prf, statement) in prfs.zip(stmt.statements)) {
      ctxEqual(ctx, prf.ctx)
      proofTreeTermCorrespondence(prf, statement)
    }
  }
}

class ItePrf(
    ctx: Scope,
    stmt: IfThenElse,
    type: Type,
    val condPrf: BooleanProofTree,
    val thenPrf: SequenceOfStatementsPrf,
    val elsePrf: SequenceOfStatementsPrf
) : StatementProofTree(ctx, stmt, type, "If: $stmt -> $type", condPrf) {

  init {
    statmentType(stmt, type)
    proofTreeTermCorrespondence(condPrf, stmt.cond)
    proofTreeTermCorrespondence(thenPrf, stmt.thenBlock)
    proofTreeTermCorrespondence(elsePrf, stmt.elseBlock)
    ctxEqual(ctx, condPrf.ctx, thenPrf.ctx, elsePrf.ctx)
  }

  override fun print(indent: String) {
    println("$indent$desc")
    children.forEach { it.print("$indent  ") }
    thenPrf.print("$indent  ")
    elsePrf.print("$indent  ")
  }
}

class WhilePrf(
    ctx: Scope,
    stmt: While,
    type: Type,
    val condPrf: BooleanProofTree,
    val invariantPrf: BooleanProofTree,
    val loopPrf: SequenceOfStatementsPrf
) : StatementProofTree(ctx, stmt, type, "While: $stmt -> $type", condPrf) {

  init {
    statmentType(stmt, type)
    proofTreeTermCorrespondence(condPrf, stmt.head)
    proofTreeTermCorrespondence(invariantPrf, stmt.invariant)
    proofTreeTermCorrespondence(loopPrf, stmt.body)
    ctxEqual(ctx, condPrf.ctx, invariantPrf.ctx, loopPrf.ctx)
  }

  override fun print(indent: String) {
    println("$indent$desc")
    children.forEach { it.print("$indent  ") }
    loopPrf.print("$indent  ")
  }
}

class PrintPrf(ctx: Scope, stmt: Print, type: Type, val valuePrfs: List<ArithmeticProofTree>) :
    StatementProofTree(ctx, stmt, type, "Print: $stmt -> $type") {

  init {
    statmentType(stmt, type)
    for ((prf, expr) in valuePrfs.zip(stmt.values)) {
      proofTreeTermCorrespondence(prf, expr)
    }
    ctxEqual(*valuePrfs.stream().map { it.ctx }.toList().toTypedArray())
  }
}

class FailPrf(ctx: Scope, stmt: Fail, type: Type) :
    StatementProofTree(ctx, stmt, type, "Fail: $stmt -> $type") {

  init {
    statmentType(stmt, type)
  }
}
