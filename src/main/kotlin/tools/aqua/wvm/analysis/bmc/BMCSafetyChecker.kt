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

package tools.aqua.wvm.analysis.bmc

import tools.aqua.wvm.machine.Context
import tools.aqua.wvm.machine.Output

class BMCSafetyChecker(val context: Context, val out: Output = Output()) {
  val transitionSystem = TransitionSystem(context)

  fun check(max_bound: Int = 10): Boolean {
    var success = true
    // Implement the BMC safety checking logic here
    // This is a placeholder for the actual implementation
    out.println("BMC Safety Checker is not yet implemented.")

    // TODO: Build Transition System

    // TODO: Check for safety violations
    // while loop for increasing bound
    for (bound in 1..max_bound) {

      out.println("Checking ${bound}-safety:")
      // TODO: Generate konstraints for the current bound
      // Put into SMT solver
      // TODO: Check satisfiability
      // if (satisfiable) {
      val sat = true
      out.println("${bound}-safety is ${if (sat) "violated" else "fulfilled"}.")
      success = success and !sat
      if (!success) break
    }

    return success
  }
}
