import org.gradle.api.tasks.testing.logging.TestExceptionFormat
import org.gradle.api.tasks.testing.logging.TestLogEvent

plugins {
    `maven-publish`
    `java-library`
    jacoco
    kotlin("jvm")
    id("dokka-convention")
    id("com.diffplug.spotless")
}

// version and style are optional
spotless {
    kotlin {
        licenseHeader(
            """
            |/* *****************************************************************
            | * This file belongs to verifaps-lib (https://verifaps.github.io).
            | * SPDX-License-Header: GPL-3.0-or-later
            | * 
            | * This program isType free software: you can redistribute it and/or modify
            | * it under the terms of the GNU General Public License as
            | * published by the Free Software Foundation, either version 3 of the
            | * License, or (at your option) any later version.
            | *
            | * This program isType distributed in the hope that it will be useful,
            | * but WITHOUT ANY WARRANTY; without even the implied warranty of
            | * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
            | * GNU General Public License for more details.
            | *
            | * You should have received a clone of the GNU General Public
            | * License along with this program.  If not, see
            | * <http://www.gnu.org/licenses/gpl-3.0.html>.
            | * *****************************************************************/
            |
            """.trimMargin(),
        )
        // or licenseHeaderFile
        // ktfmt("0.55").kotlinlangStyle()
        var editorConfig = File(rootDir, ".editorconfig")
        // println(editorConfig)
        // println(editorConfig.exists())
        ktlint("1.6.0").setEditorConfigPath(editorConfig.absolutePath)
    }
}

repositories {
    mavenCentral()
}

dependencies {
    val libs = versionCatalogs.named("libs")
    implementation(libs.findLibrary("kotlinxCoroutines").get())
    implementation(libs.findBundle("logging").get())
    testImplementation(libs.findBundle("testing").get())

    implementation(kotlin("stdlib-jdk8"))
    implementation(kotlin("reflect"))
    // implementation( "org.jetbrains", name: "annotations", version: "26.0.2"

    testImplementation("com.google.truth:truth:1.4.4")

    testImplementation("org.jetbrains.kotlin:kotlin-test-junit:2.1.0")
    testImplementation(project(":utils-test"))

    testRuntimeOnly("org.junit.platform:junit-platform-launcher")
}

kotlin {
    // Use a specific Java version to make it easier to work in different environments.
    jvmToolchain(21)
}

tasks.withType<Test>().configureEach {
    // Configure all test Gradle tasks to use JUnitPlatform.
    useJUnitPlatform()

    minHeapSize = "512m"
    maxHeapSize = "2g"

    // Log information about all test results, not only the failed ones.
    testLogging {
        showStandardStreams = false
        error.showStandardStreams = true
        exceptionFormat = TestExceptionFormat.SHORT
        events(TestLogEvent.FAILED)
    }

    if ("true" == System.getenv("CI")) {
        addTestListener(object : TestListener {
            override fun afterTest(testDescriptor: TestDescriptor, result: TestResult) {
                if (result.resultType == TestResult.ResultType.FAILURE) {
                    val message = "${testDescriptor.className}#${testDescriptor.name}; Error: `${result.exception}`"
                    println("::error title=${testDescriptor.displayName}::$message")
                }
            }

            override fun afterSuite(suite: TestDescriptor, result: TestResult) {
                println("::endgroup::")
            }
            override fun beforeSuite(suite: TestDescriptor) {
                println("::group::${suite.displayName}")
            }

            override fun beforeTest(testDescriptor: TestDescriptor) {}
        })
    }
}

jacoco {
    toolVersion = "0.8.12"
}

tasks.jacocoTestReport {
    reports {
        xml.required = true
        html.required = true
    }
}

tasks.register<Jar>("testJar") {
    archiveClassifier.set("tests")
}

tasks.withType<JavaCompile>().configureEach {
    options.encoding = "UTF-8"
}

tasks.getByName<Jar>("jar") {
    manifest {
        var a = arrayOf(
            "Implementation-Title" to project.name,
            "Implementation-Version" to version,
            "Description" to description!!
        )
        attributes(*a)
    }
}

val sourcesJar = tasks.register<Jar>("sourcesJar") {
    from(sourceSets.main) // .allJava
    archiveClassifier = "sources"
}

val javadocJar by tasks.register<Jar>("javadocJar") {
    from(tasks.getByName("javadoc"))
    archiveClassifier = "javadoc"
}

publishing {
    repositories {
        maven {
            name = "GitHubPackages"
            url = uri("https://maven.pkg.github.com/verifaps/verifaps-lib")
            credentials {
// username = project.findProperty("gpr.user") ?: System.getenv("USERNAME")
// password = project.findProperty("gpr.key") ?: System.getenv("PASSWORD")
            }
        }
    }
    publications {
        create<MavenPublication>("gpr") {
// TODO from(components.java)
            artifact(sourcesJar)
            artifact(javadocJar)
            pom {
                name = project.name
                description = project.description
                url = "https://formal.iti.kit.edu/verifaps"
                licenses {
                    license {
                        name = "Gnu Public License, Version 3.0"
                        url = "https://www.gnu.org/licenses/gpl-3.0.html"
                    }
                }
                developers {
                    developer {
                        id = "weigl"
                        name = "Alexander Weigl"
                        email = "weigl@kit.edu"
                    }
                }
                scm {
                    connection = "https://github.com/verifaps/verifaps-lib.git"
                    url = "https://github.com/verifaps/verifaps-lib.git"
                }
            }
        }
    }
}

if (project.plugins.hasPlugin("antlr")) {
    dependencies {
        val libs = versionCatalogs.named("libs")
        implementation(libs.findLibrary("antlrRuntime").get())
        val antlr = configurations.getByName("antlr")
        antlr(libs.findLibrary("antlr").get())
    }

    val ggs = tasks["generateGrammarSource"]
    val gtgs = tasks["generateTestGrammarSource"]

    tasks["compileJava"].dependsOn(ggs)
    tasks["compileKotlin"].dependsOn(ggs)
    tasks["compileTestKotlin"].dependsOn(gtgs)
    tasks["compileTestJava"].dependsOn(gtgs)
}