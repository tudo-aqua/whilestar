package tools.aqua.wvm.analysis.dataflow

import tools.aqua.wvm.language.*
import tools.aqua.wvm.machine.Scope
import tools.aqua.wvm.parser.Parser

enum class Direction {
    Forward, Backward
}

enum class AnalysisType {
    Must /* Intersection*/,
    May /* Union */
}

interface Fact

fun interface Kill<F : Fact, T: Statement> {
    fun kill(fact: F, node:CFGNode<T>): Boolean
}

fun interface Gen<F : Fact, T: Statement> {
    fun gen(node:CFGNode<T>): Set<F>
}

fun interface Initialization<F: Fact> {
    fun initialize(cfg:CFG, scope:Scope) : Map<CFGNode<*>, Pair<Set<F>,Set<F>>>
}

data class DataflowAnalysis<F : Fact>(
    val direction: Direction,
    val type:AnalysisType,
    val initialization: Initialization<F>,
    val ifGen:Gen<F, IfThenElse>       = Gen { emptySet() },
    val ifKill:Kill<F, IfThenElse>     = Kill { _, _ -> false },
    val whileGen:Gen<F, While>         = Gen { emptySet() },
    val whileKill:Kill<F, While>       = Kill { _, _ -> false },
    val assignGen:Gen<F, Assignment>   = Gen { emptySet() },
    val assignKill:Kill<F, Assignment> = Kill { _, _ -> false },
    val failGen:Gen<F, Fail>           = Gen { emptySet() },
    val failKill:Kill<F, Fail>         = Kill { _, _ -> false },
    val havocGen:Gen<F, Havoc>         = Gen { emptySet() },
    val havocKill:Kill<F, Havoc>       = Kill { _, _ -> false },
    val swapGen:Gen<F, Swap>           = Gen { emptySet() },
    val swapKill:Kill<F, Swap>         = Kill { _, _ -> false },
    val printGen:Gen<F, Print>         = Gen { emptySet() },
    val printKill:Kill<F, Print>       = Kill { _, _ -> false }) {

    fun initialize(cfg:CFG, scope: Scope) : Map<CFGNode<*>, Pair<Set<F>,Set<F>>> =
        initialization.initialize(cfg, scope)

    fun next(cfg:CFG, marking:Map<CFGNode<*>, Pair<Set<F>, Set<F>>>) :
            Map<CFGNode<*>, Pair<Set<F>, Set<F>>> {
        return cfg.nodes().associateWith { node ->
            val preds = if (direction == Direction.Forward) cfg.pred(node) else cfg.succ(node)
            val inFacts : Set<F> = when(type) {
                AnalysisType.May -> preds.flatMap {
                    if (direction == Direction.Forward) marking[it]!!.second else marking[it]!!.first }.toSet()
                AnalysisType.Must -> if (preds.isEmpty()) emptySet() else {
                    val init =  if (direction == Direction.Forward) marking[preds.first()]!!.second else marking[preds.first()]!!.first
                    preds.drop(1).fold(init) { acc, n -> acc.intersect(
                        if(direction == Direction.Forward) marking[n]!!.second else marking[n]!!.first ) }
                }
            } + if (direction == Direction.Forward) marking[node]!!.first else marking[node]!!.second
            val outFacts = when(node.stmt) {
                is IfThenElse -> (inFacts.filter { !ifKill.kill(it, node as CFGNode<IfThenElse>) } +
                        ifGen.gen(node as CFGNode<IfThenElse>)).toSet()
                is While      -> (inFacts.filter { !whileKill.kill(it, node as CFGNode<While>) } +
                        whileGen.gen(node as CFGNode<While>)).toSet()
                is Assignment -> (inFacts.filter { !assignKill.kill(it, node as CFGNode<Assignment>) } +
                        assignGen.gen(node as CFGNode<Assignment>)).toSet()
                is Fail       -> (inFacts.filter { !failKill.kill(it, node as CFGNode<Fail>) } +
                        failGen.gen(node as CFGNode<Fail>)).toSet()
                is Havoc      -> (inFacts.filter { !havocKill.kill(it, node as CFGNode<Havoc>) } +
                        havocGen.gen(node as CFGNode<Havoc>)).toSet()
                is Print      -> (inFacts.filter { !printKill.kill(it, node as CFGNode<Print>) } +
                        printGen.gen(node as CFGNode<Print>)).toSet()
                is Swap       -> (inFacts.filter { !swapKill.kill(it, node as CFGNode<Swap>) } +
                        swapGen.gen(node as CFGNode<Swap>)).toSet()
            }

            if (direction == Direction.Forward)
                Pair(inFacts, outFacts)
            else
                Pair(outFacts, inFacts)
        }
    }

    fun isFixedPoint(cfg:CFG, marking:Map<CFGNode<*>, Pair<Set<F>, Set<F>>>) =
        next(cfg, marking).all { (n, f) -> f == marking[n] }

    //abstract fun check()
}



fun main() {

    val ctx = Parser(restricted = true).parse("""
vars:
  int x;
  int y;
  int z;
code:
  x := 10;
  y := 20;
  z := x + y;
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
}
