plugins {
    id("antlr")
    id("kotlin-convention")
}

description = "Library for creation and parsing of SMV files."

dependencies {
    implementation(project(":util"))
    implementation(libs.antlrRuntime)
    antlr(libs.antlr)
    implementation(libs.jdom)
}

tasks.named<AntlrTask>("generateGrammarSource") {
    arguments.addAll(
        listOf(
            "-long-messages", "-visitor",
            "-package", "edu.kit.iti.formal.smv.parser"
        )
    )
}

//compileKotlin.dependsOn(generateGrammarSource)
//compileTestKotlin.dependsOn(generateTestGrammarSource)
