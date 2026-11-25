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

import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Test
import tools.aqua.wvm.machine.Scope

class ParserTest {

  @Test
  fun testParser() {
    val ctx =
        Parser(restricted = true)
            .parse(
                """
vars:
  int x;
  int y;
  int z;
code:
  x := 10;
  y := 20;
  z := x + y;
  while (x > 0)  {
    x := x - 1;
  };
  y := 0;
""")
    println(ctx)
    ctx.execute(true)
    // println(Json.encodeToString(ctx.cfg))
  }

  @Test
  fun testRejectsOversizedArray() {
    assertThrows(IllegalArgumentException::class.java) {
      Parser().parse("vars:\n  int[${Scope.MAX_MEMORY_SIZE}] a;\ncode:\n")
    }
    assertThrows(IllegalArgumentException::class.java) {
      Parser().parse("vars:\n  int[99999999999999] a;\ncode:\n")
    }
    assertThrows(IllegalArgumentException::class.java) {
      Parser().parse("vars:\n  int[6000] a;\n  int[6000] b;\ncode:\n")
    }
    assertThrows(IllegalArgumentException::class.java) {
      Scope(emptyMap(), Scope.MAX_MEMORY_SIZE + 1)
    }
  }
}
