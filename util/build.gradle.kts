plugins{
    id("kotlin-convention")
    `java-test-fixtures`
}

description = "Util classes"

dependencies {
    testFixturesImplementation(libs.junitApi)
}