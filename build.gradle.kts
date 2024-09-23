/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2024-2023 The While* Authors
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

import com.github.gradle.node.variant.computeNodeDir
import com.github.gradle.node.variant.computeNodeExec
import org.gradle.api.plugins.JavaBasePlugin.DOCUMENTATION_GROUP
import org.gradle.api.publish.plugins.PublishingPlugin.PUBLISH_TASK_GROUP
import org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED
import org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED
import org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED

plugins {
  `maven-publish`
  signing

  alias(libs.plugins.kotlin.dokka)
  alias(libs.plugins.kotlin.jvm)
  alias(libs.plugins.kotlin.serialization)
  alias(libs.plugins.nexus.publish)
  alias(libs.plugins.node)
  alias(libs.plugins.runtime)
  alias(libs.plugins.spotless)
  alias(libs.plugins.taskTree)
  alias(libs.plugins.versions)
}

group = "tools.aqua"

version = "1.0-SNAPSHOT"

repositories { mavenCentral() }

dependencies {
  implementation(libs.clikt)
  implementation(libs.petitparser.core)
  implementation("tools.aqua:konstraints:0.1")
  testImplementation(libs.junit.jupiter)
  testRuntimeOnly(libs.junit.launcher)
}

node {
  download = true
  workDir = layout.buildDirectory.dir("nodejs")
}

tasks.dependencyUpdates {
  gradleReleaseChannel = "current"
  revision = "current"
}

spotless {
  kotlin {
    targetExclude(sourceSets.main.get().resources, sourceSets.test.get().resources)
    licenseHeaderFile(project.file("config/license/Apache-2.0-cstyle"))
    ktfmt()
  }
  kotlinGradle {
    licenseHeaderFile(project.file("config/license/Apache-2.0-cstyle"), "(plugins|import )")
    ktfmt()
  }
  format("markdown") {
    target("*.md")
    licenseHeaderFile(project.file("config/license/CC-BY-4.0-xmlstyle"), "#+")
    prettier()
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(mapOf("parser" to "markdown", "printWidth" to 100, "proseWrap" to "always"))
  }
  yaml {
    target("config/**/*.yml", ".gitlab-ci.yml", "CITATION.cff")
    licenseHeaderFile(project.file("config/license/Apache-2.0-hashmark"), "[A-Za-z-]+:")
    prettier()
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(mapOf("parser" to "yaml", "printWidth" to 100))
  }
  format("toml") {
    target("gradle/libs.versions.toml")
    licenseHeaderFile(project.file("config/license/Apache-2.0-hashmark"), """\[[A-Za-z-]+]""")
    prettier(mapOf("prettier-plugin-toml" to libs.versions.prettier.toml.get()))
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(
            mapOf(
                "plugins" to listOf("prettier-plugin-toml"),
                "parser" to "toml",
                "alignComments" to false,
                "printWidth" to 100,
            ))
  }
}

tasks.named("spotlessMarkdown") { dependsOn(tasks.npmSetup) }

tasks.named("spotlessToml") { dependsOn(tasks.npmSetup) }

tasks.named("spotlessYaml") { dependsOn(tasks.npmSetup) }

val kdocJar: TaskProvider<Jar> by
    tasks.registering(Jar::class) {
      group = DOCUMENTATION_GROUP
      archiveClassifier = "kdoc"
      from(tasks.dokkaHtml.flatMap { it.outputDirectory })
    }

val kdoc: Configuration by
    configurations.creating {
      isCanBeConsumed = true
      isCanBeResolved = false
    }

artifacts { add(kdoc.name, kdocJar) }

val javadocJar: TaskProvider<Jar> by
    tasks.registering(Jar::class) {
      group = DOCUMENTATION_GROUP
      archiveClassifier = "javadoc"
      from(tasks.dokkaJavadoc.flatMap { it.outputDirectory })
    }

java {
  withJavadocJar()
  withSourcesJar()
}

kotlin { jvmToolchain(21) }

tasks.create("fatJar", Jar::class) {
  archiveBaseName = "${project.name}-with-dependencies"
  group = "build"
  description = "Creates a self-contained fat JAR that can be used for testing WVM locally."
  manifest.attributes["Main-Class"] = "tools.aqua.wvm.MainKt"
  duplicatesStrategy = DuplicatesStrategy.EXCLUDE
  val dependencies = configurations.runtimeClasspath.get().map(::zipTree)
  from(dependencies)
  with(tasks.jar.get())
}

tasks.test {
  useJUnitPlatform()
  testLogging { events(FAILED, SKIPPED, PASSED) }
}

application { mainClass = "tools.aqua.wvm.MainKt" }

publishing {
  publications {
    create<MavenPublication>("maven") {
      from(components["java"])

      pom {
        name = "While* Virtual Machine"
        description = "An execution environment for the While* teaching language"
        url = "https://github.com/tudo-aqua/whilestar"

        licenses {
          license {
            name = "Apache-2.0"
            url = "https://www.apache.org/licenses/LICENSE-2.0"
          }
          license {
            name = "CC-BY-4.0"
            url = "https://creativecommons.org/licenses/by/4.0/"
          }
        }

        developers {
          developer {
            name = "Simon Dierl"
            email = "simon.dierl@tu-dortmund.de"
            organization = "TU Dortmund University"
          }
          developer {
            name = "Falk Howar"
            email = "falk.howar@tu-dortmund.de"
            organization = "TU Dortmund University"
          }
          developer {
            name = "Richard Stewing"
            email = "richard.stewing@tu-dortmund.de"
            organization = "TU Dortmund University"
          }
        }

        scm {
          connection = "scm:git:https://github.com:tudo-aqua/whilestar.git"
          developerConnection = "scm:git:ssh://git@github.com:tudo-aqua/whilestar.git"
          url = "https://github.com/tudo-aqua/whilestar/tree/main"
        }
      }
    }
  }
}

signing {
  setRequired { gradle.taskGraph.allTasks.any { it.group == PUBLISH_TASK_GROUP } }
  useGpgCmd()
  sign(publishing.publications["maven"])
}

nexusPublishing { this.repositories { sonatype() } }
