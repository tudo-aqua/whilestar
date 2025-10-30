package tools.aqua.wvm.analysis.dataflow

import tools.aqua.wvm.language.*

sealed interface CFG {
    fun nodes()    : List<CFGNode<*>> = emptyList()
    fun edges()    : List<CFGEdge>    = emptyList()
    fun initial()  : List<CFGNode<*>> = emptyList()
    fun final()    : List<CFGNode<*>> = emptyList()
    fun idOf(node:CFGNode<*>) : Int

    fun pred(n:CFGNode<*>): Set<CFGNode<*>> = edges().filter { it.to == n }.map { it.from }.toSet()
    fun succ(n:CFGNode<*>): Set<CFGNode<*>> = edges().filter { it.from == n }.map { it.to }.toSet()
}

data object EmptyCFG : CFG {
    override fun idOf(node: CFGNode<*>): Int = error("not a node of this cfg")
    override fun toString(): String = "[]"
}

data class CFGNode<T : Statement> (val stmt:T)

data class SimpleCFG(val node:CFGNode<*>) : CFG {
    override fun nodes(): List<CFGNode<*>> = listOf(node)
    override fun initial(): List<CFGNode<*>> = listOf(node)
    override fun final(): List<CFGNode<*>> = listOf(node)
    override fun idOf(node: CFGNode<*>): Int =
        if (node == this.node) 0 else error("not a node of this cfg")
    override fun toString(): String {
        return "n0: ${node.stmt}"
    }
}

data class CFGEdge(val from:CFGNode<*>, val to:CFGNode<*>)

data class ComplexCFG(val nodes:List<CFGNode<*>>, val edges:List<CFGEdge>,
                      val initial:List<CFGNode<*>>, val final:List<CFGNode<*>>) : CFG {
    override fun nodes(): List<CFGNode<*>> = nodes
    override fun edges(): List<CFGEdge> = edges
    override fun initial(): List<CFGNode<*>> = initial
    override fun final(): List<CFGNode<*>> = final
    override fun idOf(node: CFGNode<*>): Int =
        if (nodes.contains(node)) nodes.indexOf(node) else error("not a node of this cfg")
    override fun toString(): String =
        nodes.map { n -> "n${idOf(n)}: ${n.stmt}" }.joinToString("\n") + "\n" +
                edges.map{ e -> "n${idOf(e.from)} -> n${idOf(e.to)}"}.joinToString("\n")
}

private fun compose(first:CFG, second:List<CFG>) : CFG {
    if(first is EmptyCFG) error("First argument to compose must not be empty")
    if (second.isEmpty() or second.all { it is EmptyCFG }) return first
    val nodes = first.nodes() + second.flatMap { it.nodes() }
    val edges = first.edges() + second.flatMap { it.edges() } + first.final().flatMap { f ->
        second.filter{ it !is EmptyCFG }.flatMap { s -> s.initial().map { CFGEdge(f, it) } }
    }
    val final = second.flatMap { it.final() } + if (second.any{ it is EmptyCFG }) first.final() else emptyList()
    return ComplexCFG(nodes, edges, first.initial(), final)
}

fun cfg(stmt: Statement) : CFG = when (stmt) {
    is IfThenElse -> compose( SimpleCFG(CFGNode(stmt)), listOf(cfg(stmt.thenBlock.statements), cfg(stmt.elseBlock.statements)) )
    is While -> {
        val whileNode = CFGNode(stmt)
        val whileBody = cfg(stmt.body.statements)
        ComplexCFG(
            whileBody.nodes() + listOf(whileNode),
            whileBody.edges() +
                    whileBody.initial().map { CFGEdge(whileNode, it) } +
                    whileBody.final().map { CFGEdge(it, whileNode) },
            listOf(whileNode),
            listOf(whileNode))}
    else -> SimpleCFG(CFGNode(stmt))
}

fun cfg(seq:List<Statement>) : CFG =
    if (seq.isEmpty()) EmptyCFG else compose(cfg(seq.first()), listOf(cfg(seq.drop(1))))

