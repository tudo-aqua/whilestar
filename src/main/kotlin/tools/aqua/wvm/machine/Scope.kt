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

import tools.aqua.wvm.language.Type

data class Scope(internal val symbols: Map<String, ElementInfo>, val size: Int) {

  data class ElementInfo(val type: Type, val address: Int, val size: Int)

  fun resolve(name: String): Int =
      symbols[name]?.address ?: throw Exception("tried to resolve unknown variable: $name")

  fun type(name: String): Type =
      symbols[name]?.type ?: throw Exception("tried to get type of unknown variable: $name")

  fun typeEqual(other: Scope): Boolean {
    val keys = symbols.keys
    val otherKeys = other.symbols.keys
    if (!keys.equals(otherKeys)) {
      return false
    }

    for (k in keys) {
      if (symbols[k]?.type != other.symbols[k]?.type) {
        return false
      }
    }
    return true
  }

  fun getNames() = symbols.keys

  fun defines(name: String) = symbols.containsKey(name)

  override fun toString(): String =
      "Variable addresses: ${symbols.map{"${it.value.type} ${it.key} -> ${it.value.address}"}}"

  fun gammaPrint(): String = symbols.map { "${it.key}:${it.value.type}" }.joinToString(",")
}
