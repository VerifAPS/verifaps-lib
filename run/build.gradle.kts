plugins {
    id("kotlin-convention")
}

description = "Interpreter for StructuredText"
group = "test"

dependencies {
    implementation(project(":lang"))
    implementation(project(":smv"))
    implementation(project(":xml"))
    implementation(project(":symbex"))
}
