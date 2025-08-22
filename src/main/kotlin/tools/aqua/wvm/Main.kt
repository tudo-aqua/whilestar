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
import tools.aqua.wvm.analysis.inductiveVerification.BMCSafetyChecker
import tools.aqua.wvm.analysis.hoare.WPCProofSystem
import tools.aqua.wvm.analysis.typesystem.TypeChecker
import tools.aqua.wvm.language.SequenceOfStatements
import tools.aqua.wvm.machine.Output
import tools.aqua.wvm.parser.Parser

class While : CliktCommand() {

  private val verbose: Boolean by option("-v", "--verbose", help = "enable verbose mode").flag()

  private val run: Boolean by option("-r", "--run", help = "run the code").flag()

  private val typecheck: Boolean by option("-t", "--typecheck", help = "run type check").flag()

  private val proof: Boolean by
      option("-p", "--proof", help = "proof (instead of execution)").flag()

  private val bmc: Boolean by option("-b", "--bmc", help = "run bmc checker").flag()

  private val externalInput: Boolean by
      option("-i", "--input", help = "enables input for external variables").flag()

  private val filename: String by argument(help = "source file to interpret")

  override fun run() {

    if (!run && !typecheck && !proof && !bmc) {
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
        println(context.pre)
        println(context.post)
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
        wps.proof()
        println("=============================================")
      }

      if (bmc) {
        println("=========== Running BMC checker: ===========")
        val out = Output()
        val bmcChecker = BMCSafetyChecker(context, out, verbose)
        bmcChecker.check(maxBound = 10)
        println("=============================================")
      }

      if (run) {
        println("============ Running program: ===============")
        val trace = context.execute(verbose)
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
