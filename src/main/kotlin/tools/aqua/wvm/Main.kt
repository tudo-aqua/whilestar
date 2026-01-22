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
import tools.aqua.wvm.analysis.hoare.SMTSolver
import tools.aqua.wvm.analysis.hoare.WPCProofSystem
import tools.aqua.wvm.analysis.inductiveVerification.BMCSafetyChecker
import tools.aqua.wvm.analysis.inductiveVerification.KInductionChecker
import tools.aqua.wvm.analysis.inductiveVerification.KInductionCheckerWithBMC
import tools.aqua.wvm.analysis.typesystem.TypeChecker
import tools.aqua.wvm.language.SequenceOfStatements
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

var externCounter: Int = 0

class While : CliktCommand() {

  private val verbose: Boolean by option("-v", "--verbose", help = "enable verbose mode").flag()

  private val run: Boolean by option("-r", "--run", help = "run the code").flag()

  private val typecheck: Boolean by option("-t", "--typecheck", help = "run type check").flag()

  private val symbolic: Boolean by option("-s", "--symbolic", help = "run code symbolicly").flag()

  private val proof: Boolean by
      option("-p", "--proof", help = "proof (instead of execution)").flag()

  private val bmc: Boolean by option("-b", "--bmc", help = "run bmc checker").flag()

  private val kInd: Boolean by option("-k", "--kind", help = "run k-induction checker").flag()

  private val useWhileInvariant by
      option("--kInd-inv", help = "use while invariant in k-induction").flag()

  // TODO: Make sure this is properly implemented throughout the codebase
  private val booleanEvaluation: Boolean by
      option("-B", "--boolean-eval", help = "enable boolean evaluation for gpdr").flag()

  private val externalInput: Boolean by
      option("-i", "--input", help = "enables input for external variables").flag()

  private val filename: String by argument(help = "source file to interpret")

  override fun run() {

    if (!run && !typecheck && !proof && !symbolic && !bmc && !kInd) {
      echoFormattedHelp()
      exitProcess(1)
    }

    try {
      val source = File(filename).readText()
      val context = Parser.parse(source)
      if (externalInput) {
        context.input = Scanner(System.`in`)
      }

      if (verbose) {
        println("=============================================")
        println(context.scope)
        println(SequenceOfStatements(context.program).toIndentedString(""))
        println("Pre-Condition: " + context.pre)
        println("Post-Condition: " + context.post)
        println("=============================================")
      }

      if (typecheck) {
        println("=========== Running type checker: ===========")
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
        println("=========== Running proof system: ===========")
        val out = Output()
        val wps = WPCProofSystem(context, out)
        val result = wps.proof()
        println("# Safe: $result")
        println("# NumberOfSMTCalls: ${SMTSolver.numberOfSMTCalls}")
        SMTSolver.resetCallCounters()
        println("=============================================")
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

      if (run) {
        println("============ Running program: ===============")
        val trace = context.execute(verbose || symbolic, symbolic, booleanEvaluation)
        if (verbose) {
          println("Execution Tree:")
          print(trace.first.toIndentString(""))
        }
        if (symbolic) {
          if (verbose) {
            println("Unsafe leaf nodes:")
            for (leaf in trace.second) {
              println("====================")
              println(leaf.toIndentString(""))
            }
          }
          println("The program is ${if (trace.second.isEmpty()) "" else "un"}safe.")
        }
        if (verbose) println()
        println("=============================================")
      }
    } catch (e: Exception) {
      println("ERROR: ${e.message}")
      if (verbose) {
        e.printStackTrace()
      }
    }
  }
}

fun main(args: Array<String>) = While().main(args)
