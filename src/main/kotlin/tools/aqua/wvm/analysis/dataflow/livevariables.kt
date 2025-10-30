package tools.aqua.wvm.analysis.dataflow

class LVFact(val varname:String, val node: CFGNode<*>) : Fact {
    override fun hashCode(): Int = varname.hashCode()
    override fun equals(other: Any?): Boolean =
        other is LVFact && other.varname == varname
    override fun toString(): String = varname
}

val LVAnalysis = DataflowAnalysis(
    direction = Direction.Backward, type = AnalysisType.May,
    initialization = { c, s ->
        c.nodes().associateWith { node -> Pair(emptySet(),emptySet()) }},
    assignGen = { node ->
        varsInExpr(node.stmt.expr).map { LVFact(it, node) }.toSet() },
    assignKill = { fact, node ->
        varsInExpr(node.stmt.addr).contains(fact.varname) },
    swapKill = { fact, node ->
        varsInExpr(node.stmt.left).contains(fact.varname) ||
        varsInExpr(node.stmt.right).contains(fact.varname)  },
    havocKill = { fact, node ->
        varsInExpr(node.stmt.addr).contains(fact.varname) },
    printGen = { node ->
        node.stmt.values.map{ varsInExpr(it) }.flatten().map { LVFact(it, node) }.toSet() },
    whileGen = { node ->
        varsInExpr(node.stmt.head).map { LVFact(it, node) }.toSet() },
    ifGen = { node ->
        varsInExpr(node.stmt.cond).map { LVFact(it, node) }.toSet() },
)

