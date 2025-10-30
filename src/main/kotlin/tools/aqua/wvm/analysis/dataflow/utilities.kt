package tools.aqua.wvm.analysis.dataflow

import tools.aqua.wvm.language.*

fun varsInExpr(expr: Expression<*>): Set<String> = when (expr) {
    is ValAtAddr -> varsInExpr(expr.addr)
    is Variable -> setOf(expr.name)
    is NumericLiteral -> emptySet()
    is Add -> varsInExpr(expr.left) + varsInExpr(expr.right)
    is Sub -> varsInExpr(expr.left) + varsInExpr(expr.right)
    is Gt -> varsInExpr(expr.left) + varsInExpr(expr.right)
    else -> error("Unsupported expression for dataflow analysis: $expr")
}

fun varsInStmt(stmt: Statement): Set<String> = when (stmt) {
    is IfThenElse -> varsInExpr(stmt.cond) + varsInSeq(stmt.thenBlock) + varsInSeq(stmt.elseBlock)
    is While -> varsInExpr(stmt.head) + varsInSeq(stmt.body) // todo: invariant?
    is Assignment -> varsInExpr(stmt.addr) + varsInExpr(stmt.expr)
    is Fail -> emptySet()
    is Havoc -> varsInExpr(stmt.addr)
    is Swap -> varsInExpr(stmt.left) + varsInExpr(stmt.right)
    is Print -> stmt.values.flatMap { varsInExpr(it) }.toSet()
}

fun varsInSeq(seq: SequenceOfStatements): Set<String> =
    seq.statements.flatMap { varsInStmt(it) }.toSet()

fun varsInCFG(cfg: CFG): Set<String> =
    cfg.nodes().flatMap { varsInStmt(it.stmt) }.toSet()