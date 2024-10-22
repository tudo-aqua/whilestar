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

import java.io.File
import org.junit.jupiter.api.Test
import tools.aqua.wvm.language.SequenceOfStatements
import tools.aqua.wvm.parser.Parser

class TypeCheckerTest {

  fun run(filename: String, shouldFail: Boolean = false) {
    val source = File(filename).readText()
    val context = Parser.parse(source)

    println("==== generating type correctness proof: =====")
    val checker = TypeChecker(context.scope)
    // println(SequenceOfStatements(context.program))
    try {
      val proof = checker.checkExternalCheck(SequenceOfStatements(context.program))
    } catch (e: Exception) {
      if (shouldFail) {
        return
      }
      throw e
    }
  }

  @Test fun test01() = run("examples/array/ex1.w")

  @Test fun test02() = run("examples/array/ex2.w")

  @Test fun test03() = run("examples/assignment/ex1.w")

  @Test fun test04() = run("examples/assignment/ex2.w")

  @Test fun test05() = run("examples/assignment/ex3.w")

  @Test fun test06() = run("examples/if/ex1.w")

  @Test fun test07() = run("examples/pointer/ex1.w")

  @Test fun test08() = run("examples/pointer/ex2.w")

  @Test fun test09() = run("examples/pointer/ex3.w")

  @Test fun test10() = run("examples/while/ex1.w")

  @Test fun test11() = run("examples/assignment/ex4.w")

  @Test fun test12() = run("examples/array/selectionsort.w")

  @Test fun test13() = run("examples/pointer/ex4.w", true)

  @Test fun test14() = run("examples/pointer/ex5.w")

  @Test fun test15() = run("examples/array/dyn-mem.w")

  @Test fun test16() = run("examples/array/nesting.w")

  @Test fun test17() = run("examples/while/ackermann.w")

  @Test fun test18() = run("examples/while/collatz.w")

  @Test fun test19() = run("examples/swap/ex1.w")

  @Test fun test20() = run("examples/swap/ex2.w")

  @Test fun test21() = run("examples/havoc/ex1.w")

  @Test fun test22() = run("examples/havoc/ex2.w")

  @Test fun test23() = run("examples/while/ex2.w")
}
