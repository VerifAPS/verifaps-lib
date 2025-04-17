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
    layout.buildDirectory.dir("generated-src/antlr/main/")


repositories {
    mavenCentral()
    maven { url = URI.create("https://jitpack.io") }
}

dependencies {
    api(project(":symbex"))

    antlr(libs.antlr)
    api(libs.clickt)

    implementation("io.ktor:ktor-html-builder:1.6.8")

    api("com.github.jferard:fastods:0.8.1")
    api("com.github.doyaaaaaken:kotlin-csv-jvm:1.10.0")
}

sourceSets {
    main {
        java {
            srcDirs("src/main/java", antlrOutputDir.get().asFile)
        }
    }
}


val generateGrammarSource = tasks.named<AntlrTask>("generateGrammarSource") {
    outputDirectory = antlrOutputDir.get().dir("edu/kit/iti/formal/automation/testtables/grammar").asFile
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

tasks["dokkaHtmlPartial"].dependsOn(generateGrammarSource)