plugins {
    id("kotlin-convention")
}

description = "iec-symbex"
dependencies {
    api( project(":lang"))
    api( project(":smv"))
    api(project(":smt"))
}
