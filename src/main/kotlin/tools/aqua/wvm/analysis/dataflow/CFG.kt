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

data class CFGEdge(val from: CFGNode<*>, val to: CFGNode<*>)

data class ComplexCFG(
    val nodes: List<CFGNode<*>>,
    val edges: List<CFGEdge>,
    val initial: List<CFGNode<*>>,
    val final: List<CFGNode<*>>
) : CFG {
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
            second.filter { it !is EmptyCFG }.flatMap { s -> s.initial().map { CFGEdge(f, it) } }
          }
  val final =
      second.flatMap { it.final() } +
          if (second.any { it is EmptyCFG }) first.final() else emptyList()
  return ComplexCFG(nodes, edges, first.initial(), final)
}

fun cfg(stmt: Statement): CFG =
    when (stmt) {
      is IfThenElse ->
          compose(
              SimpleCFG(CFGNode(stmt)),
              listOf(cfg(stmt.thenBlock.statements), cfg(stmt.elseBlock.statements)))
      is While -> {
        val whileNode = CFGNode(stmt)
        val whileBody = cfg(stmt.body.statements)
        ComplexCFG(
            whileBody.nodes() + listOf(whileNode),
            whileBody.edges() +
                whileBody.initial().map { CFGEdge(whileNode, it) } +
                whileBody.final().map { CFGEdge(it, whileNode) },
            listOf(whileNode),
            listOf(whileNode))
      }
      else -> SimpleCFG(CFGNode(stmt))
    }

fun cfg(seq: List<Statement>): CFG =
    if (seq.isEmpty()) EmptyCFG else compose(cfg(seq.first()), listOf(cfg(seq.drop(1))))

fun cfgToMermaid(cfg: CFG): String {
  val nodes = cfg.nodes()
  val edges = cfg.edges()

  return buildString {
    appendLine("graph TD")

    for ((index, node) in nodes.withIndex()) {
      var nodeLabel = node.stmt.toIndentedString("")
      when (node.stmt) {
        is While -> nodeLabel = node.stmt.head.toString()
        is IfThenElse -> nodeLabel = nodeLabel.substringBefore("{")
        else -> {}
      }

      nodeLabel = nodeLabel.replace("\"", "#quot;")
      nodeLabel = nodeLabel.replace("\n", "")
      appendLine("$index[\"$index &#91${nodeLabel}&#93\"]")
    }

    for (edge in edges) {

      when (edge.from.stmt) {
        is While ->
            if (edge.from.stmt.body.head() == edge.to.stmt) {
              appendLine("${nodes.indexOf(edge.from)} --true--> ${nodes.indexOf(edge.to)}")
            } else {
              appendLine("${nodes.indexOf(edge.from)} --false--> ${nodes.indexOf(edge.to)}")
            }
        is IfThenElse ->
            if (edge.from.stmt.thenBlock.statements.first() == edge.to.stmt) {
              appendLine("${nodes.indexOf(edge.from)} --true--> ${nodes.indexOf(edge.to)}")
            } else {
              appendLine("${nodes.indexOf(edge.from)} --false--> ${nodes.indexOf(edge.to)}")
            }
        else -> appendLine("${nodes.indexOf(edge.from)} --> ${nodes.indexOf(edge.to)}")
      }
    }

    for ((index, node) in nodes.withIndex()) {
      appendLine("click $index call nodeClick(\"$index\")")
    }
  }
}
