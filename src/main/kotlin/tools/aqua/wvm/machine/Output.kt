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

package tools.aqua.wvm.machine

class Output {

  var log: Boolean = true

  private val output = mutableListOf<String>()

  fun print(message: Any?) {
    if (log) {
      output.add("$message")
    }
    kotlin.io.print(message)
  }

  fun println(message: Any?) {
    if (log) {
      output.add("${message}\n")
    }
    kotlin.io.println(message)
  }

  fun getOutput(): String = output.joinToString("") { it }
}
