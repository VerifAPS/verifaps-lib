plugins {
    id("antlr")
    id("kotlin-convention")
}

description = "iec61131lang"


dependencies {
    api(project(":util"))
    api(project(":xml"))

    api("com.github.ajalt.clikt:clikt:5.0.2")

    testImplementation("org.mdkt.compiler:InMemoryJavaCompiler:1.3.0")
    implementation("com.squareup:javapoet:1.13.0")
}

tasks.named<AntlrTask>("generateGrammarSource") {
    maxHeapSize = "64m"
    arguments.addAll(listOf("-visitor", "-long-messages", "-package", "edu.kit.iti.formal.automation.parser"))
    //outputDirectory.set(file("${project.buildDir}/generated-src/antlr/main/edu/kit/iti/formal/automation/parser"))
}

tasks.withType<Test>().configureEach {
    exclude("**/SFCLangParserTest.class")
}
