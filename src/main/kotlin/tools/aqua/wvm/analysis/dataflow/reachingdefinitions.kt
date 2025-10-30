package tools.aqua.wvm.analysis.dataflow

sealed interface RDFact : Fact {
    fun varname(): String
}
data class RDInitFact(val varname:String, val init:Boolean) : RDFact {
    override fun varname() = varname
    override fun toString(): String = "($varname, ${if (init) "init" else "?"})"
}
data class RDWriteFact(val varname:String, val node: CFGNode<*>) : RDFact {
    override fun varname() = varname
    override fun toString(): String = "($varname, write)"
}
data class RDHavocFact(val varname:String, val node: CFGNode<*>) : RDFact {
    override fun varname() = varname
    override fun toString(): String = "($varname, havoc)"
}

val RDAnalysis = DataflowAnalysis(
    direction = Direction.Forward, type = AnalysisType.May,
    initialization = { c, s ->
        c.nodes().associateWith { node -> Pair(
            if (!c.initial().contains(node)) emptySet()
            else  varsInCFG(c).map { RDInitFact(it, s.getNames().contains(it)) }.toSet(),
            emptySet())
        }},
    assignGen = { node ->
        val vrs = varsInExpr(node.stmt.addr)
        vrs.map { RDWriteFact(it, node) }.toSet()
    },
    assignKill = { fact, node ->
        varsInStmt(node.stmt).contains(fact.varname())
    },
    swapGen = { node ->
        val vrs = varsInExpr(node.stmt.left) + varsInExpr(node.stmt.right)
        vrs.map { RDWriteFact(it, node) }.toSet()
    },
    swapKill = { fact, node ->
        varsInStmt(node.stmt).contains(fact.varname())
    },
    havocGen = { node ->
        val vrs = varsInExpr(node.stmt.addr)
        vrs.map { RDHavocFact(it, node) }.toSet()
    },
    havocKill = { fact, node ->
        varsInStmt(node.stmt).contains(fact.varname())
    }
)