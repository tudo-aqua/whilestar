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

package tools.aqua.wvm.parser

import java.math.BigInteger
import org.petitparser.parser.Parser
import org.petitparser.parser.combinators.ChoiceParser
import org.petitparser.parser.combinators.SequenceParser
import org.petitparser.parser.combinators.SettableParser.undefined
import org.petitparser.parser.primitive.CharacterParser.*
import org.petitparser.parser.primitive.StringParser.of
import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Scope

operator fun Parser.plus(other: Parser): ChoiceParser = or(other)

operator fun Parser.times(other: Parser): SequenceParser = seq(other)

infix fun Parser.trim(both: Parser): Parser = trim(both)

object Parser {
  private val arraySizeLimit = 255

  private val whitespaceCat = anyOf(" \t\r\n", "space, tab, or newline expected")
  private val digitCat = range('0', '9')
  private val letterCat = range('A', 'Z') + range('a', 'z')

  private val numeral =
      ((of('0') + (range('1', '9') * digitCat.star()))).flatten() trim whitespaceCat

  private val simpleSymbol =
      (letterCat * (letterCat + digitCat).star()).flatten() trim whitespaceCat

  // all printable characters that are not double quotes
  private val anythingButQuotes =
      whitespaceCat +
          range('\u0020', '"' - 1) +
          range('"' + 1, '\u007E') +
          range('\u0080', '\u00FF')

  internal val string =
      (of("\"") *
              (anythingButQuotes.star() +
                  ((anythingButQuotes.star() * of("\"\"") * anythingButQuotes.star()).star())) *
              of("\""))
          .flatten()

  private val identifier = simpleSymbol.map { id: String -> id }

  private val lparen = of('(') trim whitespaceCat
  private val rparen = of(')') trim whitespaceCat
  private val lsbr = of('[') trim whitespaceCat
  private val rsbr = of(']') trim whitespaceCat
  private val lcbr = of('{') trim whitespaceCat
  private val rcbr = of('}') trim whitespaceCat
  private val range = of("..") trim whitespaceCat

  private val star = of('*') trim whitespaceCat
  private val plus = of('+') trim whitespaceCat
  private val minus = of('-') trim whitespaceCat
  private val slash = of('/') trim whitespaceCat
  private val percent = of('%') trim whitespaceCat
  private val amp = of('&') trim whitespaceCat

  private val eq = of('=') trim whitespaceCat
  private val gt = of('>') trim whitespaceCat
  private val gte = of(">=") trim whitespaceCat
  private val lt = of('<') trim whitespaceCat
  private val lte = of("<=") trim whitespaceCat
  private val imply = of("=>") trim whitespaceCat
  private val equiv = of("<=>") trim whitespaceCat
  private val and = of("and") trim whitespaceCat
  private val or = of("or") trim whitespaceCat
  private val not = of("not") trim whitespaceCat

  private val comma = of(',') trim whitespaceCat
  private val colon = of(':') trim whitespaceCat
  private val semicolon = of(';') trim whitespaceCat

  private val trueKW = of("true") trim whitespaceCat
  private val falseKW = of("false") trim whitespaceCat

  private val intKW = of("int") trim whitespaceCat
  private val vars = of("vars") trim whitespaceCat
  private val code = of("code") trim whitespaceCat
  private val pre = of("pre") trim whitespaceCat
  private val post = of("post") trim whitespaceCat

  private val assign = of(":=") trim whitespaceCat
  private val ifKW = of("if") trim whitespaceCat
  private val elseKW = of("else") trim whitespaceCat
  private val whileKW = of("while") trim whitespaceCat
  private val swapKW = of("swap") trim whitespaceCat
  private val printKW = of("print") trim whitespaceCat
  private val havocKW = of("extern") trim whitespaceCat
  private val failKW = of("fail") trim whitespaceCat
  private val assertKW = of("assert") trim whitespaceCat

  private val invariant = of("invariant") trim whitespaceCat
  private val negNumeral = numeral + (minus * numeral)

  private fun negNumeralToInt(n: Any): BigInteger {
    return when (n) {
      is List<*> -> (n[1] as String).toBigInteger().unaryMinus()
      is String -> n.toBigInteger()
      else -> throw Exception("Unkown numeral $n")
    }
  }

  private val arithExpr = undefined()
  private val booleanExpr = undefined()

  private val deref = undefined()

  init {
    deref.set(
        identifier.map { result: String -> Variable(result) } +
            (star * deref).map { results: List<Any> -> DeRef(results[1] as AddressExpression) })
  }

  private val addressExpr =
      (deref * lsbr * arithExpr * rsbr).map { results: List<Any> ->
        ArrayAccess(ValAtAddr(results[0] as AddressExpression), results[2] as ArithmeticExpression)
      } + deref.map { deref: AddressExpression -> deref }

  private val arithAtom =
      (lparen * arithExpr * rparen).map { results: List<Any> -> results[1] } +
          addressExpr.map { addr: AddressExpression -> ValAtAddr(addr) } +
          (amp * identifier).map { results: List<Any> ->
            VarAddress(Variable(results[1] as String))
          } +
          numeral.map { numeral: String -> NumericLiteral(numeral.toBigInteger()) }

  init {
    arithExpr.set(
        (arithAtom * plus * arithAtom).map { results: List<Any> ->
          Add(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
        } +
            (arithAtom * minus * arithAtom).map { results: List<Any> ->
              Sub(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
            } +
            (arithAtom * star * arithAtom).map { results: List<Any> ->
              Mul(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
            } +
            (arithAtom * slash * arithAtom).map { results: List<Any> ->
              Div(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
            } +
            (arithAtom * percent * arithAtom).map { results: List<Any> ->
              Rem(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
            } +
            (minus * arithAtom).map { results: List<Any> ->
              UnaryMinus(results[1] as ArithmeticExpression)
            } +
            arithAtom.map { atom: ArithmeticExpression -> atom })
  }

  private val booleanAtom =
      (lparen * booleanExpr * rparen).map { results: List<Any> -> results[1] } +
          (arithExpr * gt * arithExpr).map { results: List<Any> ->
            Gt(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
          } +
          (arithExpr * gte * arithExpr).map { results: List<Any> ->
            Gte(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
          } +
          (arithExpr * eq * eq.star() * arithExpr).map { results: List<Any> ->
            Eq(
                results[0] as ArithmeticExpression,
                results[3] as ArithmeticExpression,
                (results[2] as List<*>).size)
          } +
          (arithExpr * lt * arithExpr).map { results: List<Any> ->
            Lt(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
          } +
          (arithExpr * lte * arithExpr).map { results: List<Any> ->
            Lte(results[0] as ArithmeticExpression, results[2] as ArithmeticExpression)
          } +
          trueKW.map { _: Any -> True } +
          falseKW.map { _: Any -> False }

  init {
    booleanExpr.set(
        (booleanAtom * and * booleanAtom).map { results: List<Any> ->
          And(results[0] as BooleanExpression, results[2] as BooleanExpression)
        } +
            (booleanAtom * or * booleanAtom).map { results: List<Any> ->
              Or(results[0] as BooleanExpression, results[2] as BooleanExpression)
            } +
            (booleanAtom * imply * booleanAtom).map { results: List<Any> ->
              Imply(results[0] as BooleanExpression, results[2] as BooleanExpression)
            } +
            (booleanAtom * equiv * booleanAtom).map { results: List<Any> ->
              Equiv(results[0] as BooleanExpression, results[2] as BooleanExpression)
            } +
            (not * booleanAtom).map { results: List<Any> -> Not(results[1] as BooleanExpression) } +
            booleanAtom.map { atom: BooleanExpression -> atom })
  }

  private val stmt = undefined()
  private val seqOfStmts = undefined()

  private val exprList =
      (comma * arithExpr).star().map { results: List<Any> ->
        results.filterIsInstance<List<*>>().map { it[1] as ArithmeticExpression }
      }

  private val condition = (lparen * booleanExpr * rparen).map { results: List<Any> -> results[1] }

  private val block = (lcbr * seqOfStmts * rcbr).map { results: List<Any> -> results[1] }

  private val invar =
      (invariant * lparen * booleanExpr * rparen).map { results: List<Any> -> results[2] }

  init {
    stmt.set(
        (addressExpr * assign * arithExpr * semicolon).map { results: List<Any> ->
          Assignment(results[0] as AddressExpression, results[2] as ArithmeticExpression)
        } +
            (swapKW * addressExpr * and * addressExpr * semicolon).map { results: List<Any> ->
              Swap(results[1] as AddressExpression, results[3] as AddressExpression)
            } +
            (havocKW * addressExpr * negNumeral * range * negNumeral * semicolon).map {
                results: List<Any> ->
              Havoc(
                  results[1] as AddressExpression,
                  negNumeralToInt(results[2]),
                  (negNumeralToInt(results[4]) + BigInteger.ONE))
            } +
            (ifKW * condition * block * elseKW * block * semicolon).map { results: List<Any> ->
              IfThenElse(
                  results[1] as BooleanExpression,
                  results[2] as SequenceOfStatements,
                  results[4] as SequenceOfStatements)
            } +
            (whileKW * condition * invar.optional(True) * block * semicolon).map {
                results: List<Any> ->
              While(
                  results[1] as BooleanExpression,
                  results[3] as SequenceOfStatements,
                  results[2] as BooleanExpression)
            } +
            (printKW * string * exprList * semicolon).map { results: List<Any> ->
              @Suppress("UNCHECKED_CAST")
              Print(
                  (results[1] as String).slice(1 ..< (results[1] as String).length - 1),
                  results[2] as List<ArithmeticExpression>)
            } +
            (failKW * string * semicolon).map { results: List<Any> ->
              Fail((results[1] as String).slice(1 ..< (results[1] as String).length - 1))
            } +
            (assertKW * condition * semicolon).map { results: List<Any> ->
              @Suppress("UNCHECKED_CAST") Assertion(results[1] as BooleanExpression)
            })
  }

  init {
    seqOfStmts.set(stmt.star().map { seq: List<Statement> -> SequenceOfStatements(seq) })
  }

  private fun buildType(i: Int): Type = if (i == 0) BasicType.INT else Pointer(buildType(i - 1))

  private val typeSize =
      (lsbr * numeral * rsbr).map { results: List<Any> ->
	val arraySize = (results[1] as String).toInt()
	if (arraySize <= arraySizeLimit) {   
            Pair(
		arraySize + 1, /* +1 for the pointer to the data */
		Pointer(BasicType.INT))
	} else {
	    throw Exception("Type size is limited to ${arraySizeLimit + 1}, $arraySize + 1 requested")
	}
	} + star.star().map { results: List<Any> -> Pair(1, buildType(results.size)) }

  private val decl =
      (intKW * typeSize * identifier * semicolon).map { results: List<Any> ->
        Pair(results[2], results[1])
      }

  private fun buildScope(entries: List<Pair<String, Pair<Int, Type>>>): Scope {
    val info = HashMap<String, Scope.ElementInfo>()
    var addr = 0
    for (e in entries) {
      info[e.first] = Scope.ElementInfo(e.second.second, addr, e.second.first)
      addr += e.second.first
    }
    return Scope(info, addr)
  }

  private val declList =
      decl.star().map { decls: List<Pair<String, Pair<Int, Type>>> -> buildScope(decls) }

  private val program =
      (vars *
              colon *
              declList *
              (pre * colon * lparen * booleanExpr * rparen)
                  .optional(listOf(0, 0, 0, True, 0))
                  .map { results: List<Any> -> results[3] as BooleanExpression } *
              code *
              colon *
              seqOfStmts *
              (post * colon * lparen * booleanExpr * rparen)
                  .optional(listOf(0, 0, 0, True, 0))
                  .map { results: List<Any> -> results[3] as BooleanExpression })
          .end()
          .map { results: List<Any> ->
            Context(
                results[2] as Scope,
                (results[6] as SequenceOfStatements).statements,
                results[3] as BooleanExpression,
                results[7] as BooleanExpression)
          }

  private val parser = ChoiceParser(program)

  private val typeParser = ChoiceParser(typeSize)

  private val statementsParser = ChoiceParser(seqOfStmts)

  fun parse(input: String): Context {
    val result = parser.parse(input)
    if (result.isFailure) {
      var errLoc = result.buffer.substring(result.position)
      errLoc = errLoc.substring(0, errLoc.indexOf("\n"))
      throw Exception("${result.message} while parsing statement that starts in line: ${errLoc}")
    }
    return result.get()
  }

  fun parseType(input: String): Type = (typeParser.parse(input).get() as Pair<Int, Type>).second

  fun parseStatements(input: String): SequenceOfStatements =
      statementsParser.parse(input).get() as SequenceOfStatements
}
