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

import main.kotlin.tools.aqua.wvm.analysis.dataflow.ReachableAnalysis
import tools.aqua.wvm.language.*

sealed interface CFG {
  fun nodes(): List<CFGNode<*>> = emptyList()

  fun edges(): List<CFGEdge> = emptyList()

  fun initial(): List<CFGNode<*>> = emptyList()

  fun final(): List<CFGNode<*>> = emptyList()

  fun idOf(node: CFGNode<*>): Int

  fun pred(n: CFGNode<*>): Set<CFGNode<*>> = edges().filter { it.to == n }.map { it.from }.toSet()

  fun succ(n: CFGNode<*>): Set<CFGNode<*>> = edges().filter { it.from == n }.map { it.to }.toSet()
}

data object EmptyCFG : CFG {
  override fun idOf(node: CFGNode<*>): Int = error("not a node of this cfg")

  override fun toString(): String = "[]"
}

class CFGNode<T : Statement>(val stmt: T) {
  var id: Int = 0

  override fun toString(): String = "CFGNode(stmt=$stmt)"
}

data class SimpleCFG(val node: CFGNode<*>) : CFG {
  override fun nodes(): List<CFGNode<*>> = listOf(node)

  override fun initial(): List<CFGNode<*>> = listOf(node)

  override fun final(): List<CFGNode<*>> = listOf(node)

  override fun idOf(node: CFGNode<*>): Int =
      if (node == this.node) 0 else error("not a node of this cfg")

  override fun toString(): String {
    return "n0: ${node.stmt}"
  }
}

data class CFGEdge(val from: CFGNode<*>, val to: CFGNode<*>, val label: String? = null)

data class ComplexCFG(
    val nodes: List<CFGNode<*>>,
    val edges: List<CFGEdge>,
    val initial: List<CFGNode<*>>,
    val final: List<CFGNode<*>>
) : CFG {

  init {
    nodes.forEach { it.id = idOf(it) }
  }

  override fun nodes(): List<CFGNode<*>> = nodes

  override fun edges(): List<CFGEdge> = edges

  override fun initial(): List<CFGNode<*>> = initial

  override fun final(): List<CFGNode<*>> = final

  override fun idOf(node: CFGNode<*>): Int =
      if (nodes.contains(node)) nodes.indexOf(node) else error("not a node of this cfg")

  override fun toString(): String =
      nodes.map { n -> "n${idOf(n)}: ${n.stmt}" }.joinToString("\n") +
          "\n" +
          edges.map { e -> "n${idOf(e.from)} -> n${idOf(e.to)}" }.joinToString("\n")
}

private fun compose(first: CFG, second: List<CFG>): CFG {
  if (first is EmptyCFG) error("First argument to compose must not be empty")
  if (second.isEmpty() or second.all { it is EmptyCFG }) return first
  val nodes = first.nodes() + second.flatMap { it.nodes() }
  val edges =
      first.edges() +
          second.flatMap { it.edges() } +
          first.final().flatMap { f ->
            second
                .filter { it !is EmptyCFG }
                .flatMap { s ->
                  s.initial().map {
                    val label = if (f.stmt is While) "false" else null
                    CFGEdge(f, it, label)
                  }
                }
          }
  val final =
      second.flatMap { it.final() } +
          if (second.any { it is EmptyCFG }) first.final() else emptyList()
  return ComplexCFG(nodes, edges, first.initial(), final)
}

fun cfg(stmt: Statement): CFG =
    when (stmt) {
      is IfThenElse -> {
        val ifNode = CFGNode(stmt)
        val thenBlock = cfg(stmt.thenBlock.statements)
        val elseBlock = cfg(stmt.elseBlock.statements)
        val final =
            (if (thenBlock is EmptyCFG) listOf(ifNode) else thenBlock.final()) +
                (if (elseBlock is EmptyCFG) listOf(ifNode) else elseBlock.final())
        ComplexCFG(
            thenBlock.nodes() + elseBlock.nodes() + listOf(ifNode),
            thenBlock.edges() +
                elseBlock.edges() +
                thenBlock.initial().map { CFGEdge(ifNode, it, "true") } +
                elseBlock.initial().map { CFGEdge(ifNode, it, "false") },
            listOf(ifNode),
            final)
      }
      is While -> {
        val whileNode = CFGNode(stmt)
        val whileBody = cfg(stmt.body.statements)
        ComplexCFG(
            whileBody.nodes() + listOf(whileNode),
            whileBody.edges() +
                whileBody.initial().map { CFGEdge(whileNode, it, "true") } +
                whileBody.final().map { CFGEdge(it, whileNode) },
            listOf(whileNode),
            listOf(whileNode))
      }
      else -> SimpleCFG(CFGNode(stmt))
    }

fun cfg(seq: List<Statement>): CFG =
    if (seq.isEmpty()) EmptyCFG else compose(cfg(seq.first()), listOf(cfg(seq.drop(1))))

fun cfgToMermaid(cfg: CFG, color: List<Int> = List(cfg.nodes().size) { x -> 0 }): String {
  val nodes = cfg.nodes()
  val edges = cfg.edges()
  val initial = cfg.initial()
  val final = cfg.final()

  return buildString {
    appendLine("graph TD")
    appendLine("classDef red fill:#e35142,stroke:#333,stroke-width:1px,color:black;")
    appendLine("classDef orange fill:#ff9800,stroke:#333,stroke-width:1px,color:black;")
    appendLine("classDef green fill:#4caf50,stroke:#333,stroke-width:1px,color:black;")

    for ((index, node) in nodes.withIndex()) {

      appendLine("$index[\"$index &#91${node.stmt.toDataflowString()}&#93\"]")

      when (color[index]) {
        1 -> appendLine("class $index green")
        2 -> appendLine("class $index orange")
        3 -> appendLine("class $index red")
        else -> {}
      }
    }
    for (edge in edges) {
      val edgeLabel = edge.label?.let { "--" + edge.label + "-->" } ?: "-->"
      appendLine("${nodes.indexOf(edge.from)} $edgeLabel ${nodes.indexOf(edge.to)}")
      if (edge.from.stmt is Assertion) {
        appendLine("e${nodes.indexOf(edge.from)}(((#160;)))")
        appendLine("${nodes.indexOf(edge.from)} --false--> e${nodes.indexOf(edge.from)}")
      }
    }

    for (init in initial) {
      appendLine("s${initial.indexOf(init)}((#160;))")
      appendLine("s${initial.indexOf(init)} --> ${nodes.indexOf(init)}")
    }

    for (finalNode in final) {
      appendLine("e${final.indexOf(finalNode)}(((#160;)))")
      appendLine("${nodes.indexOf(finalNode)} --> e${final.indexOf(finalNode)}")
    }

    for ((index, node) in nodes.withIndex()) {
      val tooltip =
          node.stmt
              .toIndentedString("")
              .replace("\"", "#34;")
              .replace("<", "#60;")
              .replace(">", "#62;")
              .replace("\n", "")
      appendLine("click $index call nodeClick(\"$index\") \"$tooltip\"")
    }
  }
}

fun <F : Fact> extractColor(cfg: CFG, log: Marking<F>, analysis: DataflowAnalysis<F>): List<Int> {
  var colorList: MutableList<Int> = List(log.size) { 0 }.toMutableList()

  when (analysis) {
    ReachableAnalysis ->
        log.forEach { node, inout ->
          colorList[cfg.idOf(node)] =
              if (inout.first.isNotEmpty()) {
                if (inout.second.isNotEmpty()) {
                  1
                } else {
                  2
                }
              } else {
                3
              }
        }
    else -> {}
  }
  return colorList
}
