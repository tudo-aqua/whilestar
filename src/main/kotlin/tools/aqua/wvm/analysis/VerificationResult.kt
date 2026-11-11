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

package tools.aqua.wvm.analysis

enum class VerificationStatus {
  SAFE,
  UNSAFE,
  UNKNOWN,
}

data class VerificationResult(
    val status: VerificationStatus,
    val message: String,
    val depth: Int? = null,
    val details: String? = null,
) {
  override fun toString(): String = buildString {
    append(status)
    depth?.let { append(" at depth $it") }
    append(": ").append(message)
    details?.takeIf { it.isNotBlank() }?.let { append("\n").append(it) }
  }
}
