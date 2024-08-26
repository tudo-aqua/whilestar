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

package tools.aqua.wvm.language

sealed interface Type

enum class BasicType : Type {
  INT,
  BOOLEAN,
  UNIT;

  override fun toString(): String {
    return when (this) {
      BOOLEAN -> "boolean"
      INT -> "int"
      UNIT -> "()"
    }
  }
}

data class Pointer(val target: Type) : Type {
  override fun toString(): String {
    return "$target*"
  }
}

fun unreferenceType(type: Type): Type =
    when (type) {
      is Pointer -> type.target
      else -> type
    }

fun createNestedPointer(nesting: Int): Type {
  if (nesting <= 0) {
    return BasicType.INT
  } else {
    return Pointer(createNestedPointer(nesting - 1))
  }
}
