plugins {
    id("dokka-convention")
    id("org.sonarqube") version "7.5.0.8588"
    id("com.github.ben-manes.versions") version "0.64.0"
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