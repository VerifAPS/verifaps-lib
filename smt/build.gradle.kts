
plugins {
    id("antlr")
    id("kotlin-convention")
}

description = """
    SMT stuff
"""

dependencies {
    antlr(libs.antlr)
    implementation(libs.antlrRuntime)
    implementation(project(":util"))
}

tasks.named<AntlrTask>("generateGrammarSource") {
    arguments.addAll(listOf("-package", "edu.kit.iti.formal.smt", "-visitor"))
}

tasks["dokkaGenerateModuleHtml"].dependsOn(tasks["generateGrammarSource"])
tasks["dokkaGeneratePublicationHtml"].dependsOn(tasks["generateGrammarSource"])