/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2025 The While* Authors
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

package tools.aqua.wvm.analysis.dataflow

import org.junit.jupiter.api.Test
import tools.aqua.wvm.parser.Parser

class DataflowAnalysisTest {

  @Test
  fun test01() {
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
  z := x + k;
  extern z 1 .. 100;
  while (x > 0)  {
    x := x - 1;
  };
  y := z + k;
""")

    val cfg = cfg(ctx.program)

    println(cfg)
    println(cfg.initial())

    var marking = LVAnalysis.initialize(cfg, ctx.scope)
    println("Initial marking:")
    marking.forEach { n, f -> println("${cfg.idOf(n)} : in: ${f.first},  out: ${f.second}") }

    var changed: Boolean
    var iter = 0
    while (!LVAnalysis.isFixedPoint(cfg, marking)) {
      println("Iteration ${++iter}:")
      marking = LVAnalysis.next(cfg, marking)
      marking.forEach { n, f -> println("${cfg.idOf(n)} : in: ${f.first},  out: ${f.second}") }
    }

    println(LVAnalysis.check(cfg, marking))
  }

    @Test
    fun test02() {
        val ctx =
            Parser(restricted = true)
                .parse(
                    """
vars:
  int x;
  int y;
code:
  extern y 1 .. 100;
  while (true) {
    swap x and y;
    print "", y;
  };
""")

        val cfg = cfg(ctx.program)

        println(cfg)
        println(cfg.initial())

        var marking = TaintAnalysis.initialize(cfg, ctx.scope)
        println("Initial marking:")
        marking.forEach { n, f -> println("${cfg.idOf(n)} : in: ${f.first},  out: ${f.second}") }

        var changed: Boolean
        var iter = 0
        while (!TaintAnalysis.isFixedPoint(cfg, marking)) {
            println("Iteration ${++iter}:")
            marking = TaintAnalysis.next(cfg, marking)
            marking.forEach { n, f -> println("${cfg.idOf(n)} : in: ${f.first},  out: ${f.second}") }
        }

        println(TaintAnalysis.check(cfg, marking))
    }

    @Test
    fun test03() {
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
  z := x + k;
  extern z 1 .. 100;
  while (x > 0)  {
    x := x - 1;
  };
  y := z + k;
""")

        val cfg = cfg(ctx.program)

        println(cfg)
        println(cfg.initial())

        var marking = RDAnalysis.initialize(cfg, ctx.scope)
        println("Initial marking:")
        marking.forEach { n, f -> println("${cfg.idOf(n)} : in: ${f.first},  out: ${f.second}") }

        var changed: Boolean
        var iter = 0
        while (!RDAnalysis.isFixedPoint(cfg, marking)) {
            println("Iteration ${++iter}:")
            marking = RDAnalysis.next(cfg, marking)
            marking.forEach { n, f -> println("${cfg.idOf(n)} : in: ${f.first},  out: ${f.second}") }
        }

        println(RDAnalysis.check(cfg, marking))
    }
}
