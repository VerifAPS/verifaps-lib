plugins {
    id("kotlin-convention")
}

description = "Regression Verification Frontend"

dependencies {
    implementation(project(":lang"))
    implementation(project(":smv"))
    implementation(project(":xml"))
    implementation(project(":symbex"))
    implementation(libs.clickt)
}