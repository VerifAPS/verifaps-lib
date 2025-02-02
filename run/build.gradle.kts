plugins {
    id("kotlin-convention")
}

description = "Interpreter for StructuredText"

dependencies {
    implementation (project(":lang"))
    implementation (project(":smv"))
    implementation (project(":xml"))
    implementation (project(":symbex"))
}
