/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2024 The While* Authors
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

package tools.aqua.wvm

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import java.io.File
import java.util.*
import kotlin.system.exitProcess
import main.kotlin.tools.aqua.wvm.analysis.dataflow.ReachableAnalysis
import tools.aqua.wvm.analysis.dataflow.CFG
import tools.aqua.wvm.analysis.dataflow.DataflowAnalysis
import tools.aqua.wvm.analysis.dataflow.Fact
import tools.aqua.wvm.analysis.dataflow.LVAnalysis
import tools.aqua.wvm.analysis.dataflow.RDAnalysis
import tools.aqua.wvm.analysis.dataflow.TaintAnalysis
import tools.aqua.wvm.analysis.dataflow.cfg
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.analysis.hoare.WPCProofSystem
import tools.aqua.wvm.analysis.inductiveVerification.BMCSafetyChecker
import tools.aqua.wvm.analysis.inductiveVerification.KInductionChecker
import tools.aqua.wvm.analysis.inductiveVerification.KInductionCheckerWithBMC
import tools.aqua.wvm.analysis.typesystem.TypeChecker
import tools.aqua.wvm.language.SequenceOfStatements
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.machine.Scope
import tools.aqua.wvm.parser.Parser

class While : CliktCommand() {

  private val verbose: Boolean by option("-v", "--verbose", help = "enable verbose mode").flag()

  private val run: Boolean by option("-r", "--run", help = "run the code").flag()

  private val typecheck: Boolean by option("-t", "--typecheck", help = "run type check").flag()

  private val reachability: Boolean by
      option("-ra", "--reachability", help = "run reachability analysis").flag()

  private val liveness: Boolean by option("-l", "--liveness", help = "run liveness analysis").flag()

  private val reachingdefinitions: Boolean by
      option("-rd", "--reachingdefinitions", help = "run reaching definitions analysis").flag()

  private val taint: Boolean by option("-ta", "--taint", help = "run taint analysis").flag()

  private val proof: Boolean by
      option("-p", "--proof", help = "proof (instead of execution)").flag()

  private val bmc: Boolean by option("-b", "--bmc", help = "run bmc checker").flag()

  private val kInd: Boolean by option("-k", "--kind", help = "run k-induction checker").flag()

  private val useWhileInvariant by
      option("--kInd-inv", help = "use while invariant in k-induction").flag()

  private val externalInput: Boolean by
      option("-i", "--input", help = "enables input for external variables").flag()

  private val filename: String by argument(help = "source file to interpret")

  override fun run() {

    if (!run &&
        !typecheck &&
        !proof &&
        !liveness &&
        !reachability &&
        !reachingdefinitions &&
        !taint &&
        !bmc &&
        !kInd) {
      echoFormattedHelp()
      exitProcess(1)
    }

    try {
      val source = File(filename).readText()
      val context = Parser().parse(source)
      if (externalInput) {
        context.input = Scanner(System.`in`)
      }

      if (verbose) {
        println("=============================================")
        println(context.scope)
        println(SequenceOfStatements(context.program).toIndentedString(""))
        println(context.pre)
        println(context.post)
        println("=============================================")
      }

      if (typecheck) {
        println("==== generating type correctness proof: =====")
        val checker = TypeChecker(context.scope)
        // println(SequenceOfStatements(context.program))
        val proof = checker.check(SequenceOfStatements(context.program))
        if (proof != null) {
          proof.print("")
        }
        println("=============================================")
      }

      if (proof) {
        val out = Output()
        val wps = WPCProofSystem(context, out)
        wps.proof()
      }

      if (bmc && kInd) {
        println("======= Running BMC with k-induction =======")
        val out = Output()
        val bmcKIndChecker = KInductionCheckerWithBMC(context, out, verbose, useWhileInvariant)
        val result = bmcKIndChecker.check()
        println("# Safe: $result")
        println("# NumberOfSMTCalls: ${SMTSolver.numberOfSMTCalls}")
        SMTSolver.resetCallCounters()
        println("=============================================")
      }

      if (bmc && !kInd) {
        println("=========== Running BMC checker: ===========")
        val out = Output()
        val bmcChecker = BMCSafetyChecker(context, out, verbose)
        val result = bmcChecker.check()
        println("# Counterexample found: $result")
        println("# NumberOfSMTCalls: ${SMTSolver.numberOfSMTCalls}")
        SMTSolver.resetCallCounters()
        println("=============================================")
      }

      if (kInd && !bmc) {
        println("======== Running k-induction checker: =======")
        val out = Output()
        val kIndChecker = KInductionChecker(context, out, verbose, useWhileInvariant)
        val result = kIndChecker.check()
        println("# Safe: $result")
        println("# NumberOfSMTCalls: ${SMTSolver.numberOfSMTCalls}")
        SMTSolver.resetCallCounters()
        println("=============================================")
      }

      val cfg by lazy { cfg(context.program) }

      if (liveness) runAnalysis("Liveness", LVAnalysis, cfg, context.scope)

      if (reachingdefinitions) runAnalysis("Reaching definitions", RDAnalysis, cfg, context.scope)

      if (reachability) runAnalysis("Reachability", ReachableAnalysis, cfg, context.scope)

      if (taint) runAnalysis("Taint", TaintAnalysis, cfg, context.scope)

      if (run) {
        val trace = context.execute(verbose)
      }
    } catch (e: Exception) {
      println("ERROR: ${e.message}")
      if (verbose) {
        e.printStackTrace()
      }
    }
  }

  private fun <F : Fact> runAnalysis(
      name: String,
      analysis: DataflowAnalysis<F>,
      cfg: CFG,
      scope: Scope
  ) {
    println("==== running $name analysis: =====")
    val log = analysis.execute(cfg, scope)
    val checkResult = analysis.check(cfg, log.last())
    println(checkResult)
    println("========================================")
  }
}

fun main(args: Array<String>) = While().main(args)
