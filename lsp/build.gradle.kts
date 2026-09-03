plugins {
    id("kotlin-convention")
    application
}

application {
    mainClass = "edu.kit.iti.formal.lsp.Main"
}

description = "LSP Servers for GTT, StructuredText, and SMV languages"

dependencies {
    // Language modules
    api(project(":geteta"))
    api(project(":lang"))
    api(project(":smv"))
    
    // LSP4J
    api(libs.lsp4j)
    api(libs.lsp4jJsonrpc)
    
    // CLI
    implementation(libs.clickt)
    
    // Utilities
    implementation(libs.guava)
    implementation(libs.slf4jApi)
    
    // ANTLR runtime for accessing generated parser classes
    implementation(libs.antlrRuntime)
    
    testImplementation(kotlin("test"))
    testImplementation(libs.junitApi)
    testImplementation(libs.junitEngine)
}

// Ensure Java classes from :lang are compiled before Kotlin compilation
tasks.named("compileKotlin") {
    dependsOn(":lang:classes")
}

tasks.named<JavaCompile>("compileJava") {
    options.compilerArgs.add("-parameters")
}
