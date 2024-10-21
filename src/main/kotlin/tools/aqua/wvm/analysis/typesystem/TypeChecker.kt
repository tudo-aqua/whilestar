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

class AddressTypeReconstruction(private val ctx: Scope) {

  fun typeOf(addr: AddressExpression): Type =
      when (addr) {
        is Variable -> ctx.type(addr.name)
        is DeRef -> deref(typeOf(addr.reference))
        is ArrayAccess -> deref(typeOf(addr.array.addr))
        else -> throw Exception("fixme")
      }

  fun deref(type: Type) =
      when (type) {
        is Pointer -> type.target
        else -> throw Exception("Cannot dereference type $type")
      }
}

class ExpressionTypeReconstruction(private val ctx: Scope) {
  val addrTypes: AddressTypeReconstruction = AddressTypeReconstruction(ctx)

  // Address Expressions
  fun typeOf(variable: Variable): VarPrf {
    val type = addrTypes.typeOf(variable)
    val prf = VarPrf(ctx, variable.name, type)
    return prf
  }

  fun typeOf(deref: DeRef): DeRefPrf {
    val type = addrTypes.typeOf(deref)
    val prfR = typeOf(deref.reference)
    val prf = DeRefPrf(ctx, deref, type, prfR)
    return prf
  }

  fun typeOf(ref: VarAddress): RefPrf {
    val type = addrTypes.typeOf(ref.variable)
    val prfR = typeOf(ref.variable)
    val prf = RefPrf(ctx, ref, Pointer(type), prfR)
    return prf
  }

  fun typeOf(array: ArrayAccess): ArrayAccessPrf {
    val type = addrTypes.typeOf(array)
    val prfArray = typeOf(array.array)
    val prfIndex = typeOf(array.index)
    val prf = ArrayAccessPrf(ctx, array, type, prfArray, prfIndex)
    return prf
  }

  fun typeOf(deref: ValAtAddr): ValAtAddrPrf {
    val type = addrTypes.typeOf(deref.addr)
    val prfR = typeOf(deref.addr)
    val prf = ValAtAddrPrf(ctx, deref, type, prfR)
    return prf
  }

  // Arithmetic Expressions
  fun typeOf(literal: NumericLiteral): NumericLiteralPrf {
    val type = BasicType.INT
    val prf = NumericLiteralPrf(ctx, literal, type)
    return prf
  }

  fun typeOf(expr: Add): AdditionPrf {
    val type = BasicType.INT
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = AdditionPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Sub): SubtractionPrf {
    val type = BasicType.INT
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = SubtractionPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Mul): MultiplicationPrf {
    val type = BasicType.INT
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = MultiplicationPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Div): DivisionPrf {
    val type = BasicType.INT
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = DivisionPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Rem): RemainderPrf {
    val type = BasicType.INT
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = RemainderPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: UnaryMinus): UnaryMinusPrf {
    val type = BasicType.INT
    val prfI = typeOf(expr.negated)
    val prf = UnaryMinusPrf(ctx, expr, type, prfI)
    return prf
  }

  fun typeOf(exp: AddressExpression): AddressProofTree {
    return when (exp) {
      is Variable -> typeOf(exp)
      is ArrayAccess -> typeOf(exp)
      is DeRef -> typeOf(exp)
      else -> throw Exception("fixme")
    }
  }

  fun typeOf(exp: ArithmeticExpression): ArithmeticProofTree {
    return when (exp) {
      is VarAddress -> typeOf(exp)
      is NumericLiteral -> typeOf(exp)
      is Add -> typeOf(exp)
      is Sub -> typeOf(exp)
      is Mul -> typeOf(exp)
      is Div -> typeOf(exp)
      is Rem -> typeOf(exp)
      is UnaryMinus -> typeOf(exp)
      is ValAtAddr -> typeOf(exp)
      else -> throw Exception("fixme")
    }
    throw NotImplementedError("typeOf not implemented for $exp")
  }

  // Boolean Expressions
  fun typeOf(literal: True): TruePrf {
    val type = BasicType.BOOLEAN
    val prf = TruePrf(ctx, literal, type)
    return prf
  }

  fun typeOf(literal: False): FalsePrf {
    val type = BasicType.BOOLEAN
    val prf = FalsePrf(ctx, literal, type)
    return prf
  }

  fun typeOf(expr: Eq): EqualityPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = EqualityPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Gt): GreaterThanPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = GreaterThanPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Gte): GreaterThanOrEqualPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = GreaterThanOrEqualPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Lt): LessThanPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = LessThanPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Lte): LessThanOrEqualPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = LessThanOrEqualPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Not): NegatePrf {
    val type = BasicType.BOOLEAN
    val prfI = typeOf(expr.negated)
    val prf = NegatePrf(ctx, expr, type, prfI)
    return prf
  }

  fun typeOf(expr: And): AndPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = AndPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Or): OrPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = OrPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Imply): ImplyPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = ImplyPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(expr: Equiv): EquivPrf {
    val type = BasicType.BOOLEAN
    val prfL = typeOf(expr.left)
    val prfR = typeOf(expr.right)
    val prf = EquivPrf(ctx, expr, type, prfL, prfR)
    return prf
  }

  fun typeOf(exp: BooleanExpression): BooleanProofTree {
    when (exp) {
      is True -> return typeOf(exp)
      is False -> return typeOf(exp)
      is Eq -> return typeOf(exp)
      is Gt -> return typeOf(exp)
      is Gte -> return typeOf(exp)
      is Lt -> return typeOf(exp)
      is Lte -> return typeOf(exp)
      is Not -> return typeOf(exp)
      is And -> return typeOf(exp)
      is Or -> return typeOf(exp)
      is Imply -> return typeOf(exp)
      is Equiv -> return typeOf(exp)
      is Forall -> throw Exception("exists expressions cannot occur in while programs.")
    }
    throw NotImplementedError("typeOf not implemented for $exp")
  }

  fun <T> check(exp: Expression<T>): ExpressionProofTree? {
    try {
      when (exp) {
        is ArithmeticExpression -> return typeOf(exp)
        is AddressExpression -> return typeOf(exp)
        is BooleanExpression -> return typeOf(exp)
        else ->
            throw NotImplementedError(
                "Type checking is not implemented for unkown expression type.")
      }
    } catch (e: Exception) {
      print("Failed to type check $exp with error: \n===\n$e\n===\n")
    }

    return null
  }
}

class TypeChecker(private val ctx: Scope) {
  val exprTypes: ExpressionTypeReconstruction = ExpressionTypeReconstruction(ctx)

  fun typeOf(stmt: Assignment): AssignmentPrf {
    val type = BasicType.UNIT
    val prfL = exprTypes.typeOf(stmt.addr)
    val prfR = exprTypes.typeOf(stmt.expr)
    return AssignmentPrf(ctx, stmt, type, prfL, prfR)
  }

  fun typeOf(stmt: Swap): SwapPrf {
    val type = BasicType.UNIT
    val prfL = exprTypes.typeOf(stmt.left)
    val prfR = exprTypes.typeOf(stmt.right)
    return SwapPrf(ctx, stmt, type, prfL, prfR)
  }

  fun typeOf(stmts: SequenceOfStatements): SequenceOfStatementsPrf {
    val type = BasicType.UNIT
    val prfs = stmts.statements.map { typeOf(it) }
    return SequenceOfStatementsPrf(ctx, stmts, type, prfs)
  }

  fun typeOf(stmt: IfThenElse): ItePrf {
    val type = BasicType.UNIT
    val prfCond = exprTypes.typeOf(stmt.cond)
    val prfThen = typeOf(stmt.thenBlock)
    val prfElse = typeOf(stmt.elseBlock)
    return ItePrf(ctx, stmt, type, prfCond, prfThen, prfElse)
  }

  fun typeOf(stmt: While): WhilePrf {
    val type = BasicType.UNIT
    val prfCond = exprTypes.typeOf(stmt.head)
    val prfInv = exprTypes.typeOf(stmt.invariant)
    val prfLoop = typeOf(stmt.body)
    return WhilePrf(ctx, stmt, type, prfCond, prfInv, prfLoop)
  }

  fun typeOf(stmt: Print): PrintPrf {
    val type = BasicType.UNIT
    val prfs = stmt.values.map { exprTypes.typeOf(it) }
    return PrintPrf(ctx, stmt, type, prfs)
  }

  fun typeOf(stmt: Havoc): HavocPrf {
    val type = BasicType.UNIT
    val prfAddr = exprTypes.typeOf(stmt.addr)
    val prf = HavocPrf(ctx, stmt, type, prfAddr)
    return prf
  }

  fun typeOf(stmt: Fail): FailPrf {
    val type = BasicType.UNIT
    return FailPrf(ctx, stmt, type)
  }

  fun typeOf(stmt: Statement): StatementProofTree {
    when (stmt) {
      is Assignment -> return typeOf(stmt)
      is Swap -> return typeOf(stmt)
      is Havoc -> return typeOf(stmt)
      is IfThenElse -> return typeOf(stmt)
      is While -> return typeOf(stmt)
      is Print -> return typeOf(stmt)
      is Fail -> return typeOf(stmt)
    }
  }

  fun check(stmt: Statement): StatementProofTree? {
    try {
      return typeOf(stmt)
    } catch (e: Exception) {
      print("Failed to type check $stmt with error: \n===\n$e\n===\n")
    }

    return null
  }

  fun check(stmts: SequenceOfStatements): SequenceOfStatementsPrf? {
    try {
      return typeOf(stmts)
    } catch (e: Exception) {
      print("Failed to type check $stmts with error:\n===\n$e\n===\n")
    }
    return null
  }

  fun checkExternalCheck(stmts: SequenceOfStatements): SequenceOfStatementsPrf {
    return typeOf(stmts)
  }
}
