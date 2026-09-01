plugins {
    id("dokka-convention")
    id("org.sonarqube") version "7.4.0.8496"
    id("com.github.ben-manes.versions") version "0.61.0"
}

repositories { mavenCentral() }

dependencies {
    subprojects.forEach {
        dokka(it)
    }
}

tasks.register<JUnitMarkdownReporter>("githubReporter") {
    group = "verification"
    val i = fileTree(rootDir) {
        include("*/build/test-results/test/TEST-*.xml")
    }
    testReports.set(i)

    outputFile.set(layout.buildDirectory.file("reports/junit.md"))
}