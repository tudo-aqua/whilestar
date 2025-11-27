package main.kotlin.tools.aqua.wvm.analysis.dataflow

import tools.aqua.wvm.analysis.dataflow.AnalysisType
import tools.aqua.wvm.analysis.dataflow.*
import tools.aqua.wvm.analysis.dataflow.Direction
import tools.aqua.wvm.analysis.dataflow.Fact

object Reachable: Fact {
    override fun toString(): String = "Reachable"

}

val ReachableAnalysis =
        DataflowAnalysis(
            direction = Direction.Forward,
            type = AnalysisType.May,
            initialization = { cfg, _ ->
                val initialMarking =
                    cfg.nodes().associateWith { Pair(emptySet<Reachable>(), emptySet<Reachable>()) }.toMutableMap()
                    initialMarking[cfg.initial().first()] = Pair(setOf(Reachable), emptySet())
                    initialMarking
            },
            failKill = {_,_ -> true},
            check =
                Check {cfg, marking ->
                val unreachableNodes = marking.filter{(_, inOut) -> inOut.first.isEmpty()}.keys

                if(unreachableNodes.isEmpty()) {
                    "Reachability check OK: Every statement is reachable"
                } else {
                    val unreachableIds = unreachableNodes.map{cfg.idOf(it)}.sorted()
                    "Reachability check FAILED: The following statements are not reachable: $unreachableIds"
                }
            }
        )