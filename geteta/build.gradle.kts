import java.net.URI

plugins {
    id("kotlin-convention")
    id("antlr")
}

description = """
    Generalized Test Table
"""

version = "0.10"

val antlrOutputDir =
    file("${project.buildDir}/generated-src/antlr/main/edu/kit/iti/formal/automation/testtables/grammar")


repositories {
    mavenCentral()
    maven { url = URI.create("https://jitpack.io") }
}

dependencies {
    api(project(":symbex"))

    antlr(libs.antlr)
    api(libs.clickt)

    api("com.github.jferard:fastods:0.8.1")
    api("com.github.doyaaaaaken:kotlin-csv-jvm:1.10.0")
}

sourceSets {
    main {
        java {
            srcDirs("src/main/java", file("${project.buildDir}/generated-src/antlr/main"))
        }
    }
}


val generateGrammarSource = tasks.named<AntlrTask>("generateGrammarSource") {
    outputDirectory = antlrOutputDir
    arguments.addAll(listOf("-package", "edu.kit.iti.formal.automation.testtables.grammar", "-visitor"))
}

val compileKotlin by tasks.getting
val compileTestKotlin by tasks.getting
val compileJava by tasks.getting
val generateTestGrammarSource by tasks.getting

compileJava.dependsOn(generateGrammarSource)
compileKotlin.dependsOn(generateGrammarSource)
compileTestKotlin.dependsOn(generateTestGrammarSource)

tasks.named<Test>("test") {
    exclude(
        "**/AutomataDrawerTest.class",
        "**/SmtEncoderTest.class",
        "**/FullStackTest.class",
        "**/SMVModuleBuilderTest.class"
    )
}


