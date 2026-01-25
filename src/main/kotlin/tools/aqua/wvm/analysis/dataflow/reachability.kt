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

package main.kotlin.tools.aqua.wvm.analysis.dataflow

import tools.aqua.wvm.analysis.dataflow.*
import tools.aqua.wvm.analysis.dataflow.AnalysisType
import tools.aqua.wvm.analysis.dataflow.Direction
import tools.aqua.wvm.analysis.dataflow.Fact

object Reachable : Fact {
  override fun toString(): String = "Reachable"
}

val ReachableAnalysis =
    DataflowAnalysis(
        direction = Direction.Forward,
        type = AnalysisType.May,
        initialization = { cfg, _ ->
          val initialMarking =
              cfg.nodes()
                  .associateWith { Pair(emptySet<Reachable>(), emptySet<Reachable>()) }
                  .toMutableMap()
          initialMarking[cfg.initial().first()] = Pair(setOf(Reachable), emptySet())
          initialMarking
        },
        failKill = { _, _ -> true },
        factSetFormatter = { set -> if (set.isNotEmpty()) "reachable" else "unreachable" },
        check =
            Check { cfg, marking ->
              val unreachableNodes = marking.filter { (_, inOut) -> inOut.first.isEmpty() }.keys

              if (unreachableNodes.isEmpty()) {
                "Reachability check OK: Every statement is reachable"
              } else {
                val unreachableIds = unreachableNodes.map { cfg.idOf(it) }.sorted()
                "Reachability check FAILED: The following statements are not reachable: $unreachableIds"
              }
            })
