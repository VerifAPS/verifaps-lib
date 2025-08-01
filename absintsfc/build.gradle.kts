plugins {
    id("kotlin-convention")
}

dependencies {
    implementation("com.github.ajalt.clikt:clikt:5.0.3")
    implementation("org.graphstream:gs-core:2.0")
    implementation("org.graphstream:gs-ui:1.3")
    implementation("org.graphstream:gs-algo:2.0")

    implementation(project(":lang"))
    implementation(project(":xml"))
    implementation(project(":symbex"))
}