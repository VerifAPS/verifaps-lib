plugins {
    id("dokka-convention")
    id("org.sonarqube") version "7.2.2.6593"
    id("com.github.ben-manes.versions") version "0.53.0"
}

repositories { mavenCentral() }

dependencies {
    subprojects.forEach {
        dokka(it)
    }
}