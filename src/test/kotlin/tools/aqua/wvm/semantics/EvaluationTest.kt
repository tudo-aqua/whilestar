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

package tools.aqua.wvm.semantics

import java.io.File
import org.junit.jupiter.api.Test
import tools.aqua.wvm.parser.Parser

class EvaluationTest {
  fun run(filename: String) {
    val source = File(filename).readText()
    val context = Parser.parse(source)
    context.execute(false, symbolic = false)
  }

  @Test fun test1() = run("examples/array/ex1.w")

  @Test fun test2() = run("examples/array/ex2.w")

  @Test fun test3() = run("examples/assignment/ex1.w")

  @Test fun test4() = run("examples/assignment/ex2.w")

  @Test fun test5() = run("examples/assignment/ex3.w")

  @Test fun test6() = run("examples/if/ex1.w")

  @Test fun test7() = run("examples/pointer/ex1.w")

  @Test fun test8() = run("examples/pointer/ex2.w")

  @Test fun test9() = run("examples/pointer/ex3.w")

  @Test fun test10() = run("examples/while/ex1.w")

  @Test fun test11() = run("examples/assignment/ex4.w")

  @Test fun test12() = run("examples/array/selectionsort.w")

  @Test fun test13() = run("examples/pointer/ex4.w")
}
