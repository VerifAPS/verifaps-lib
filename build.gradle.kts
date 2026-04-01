plugins {
    id("dokka-convention")
    id("org.sonarqube") version "7.2.3.7755"
    id("com.github.ben-manes.versions") version "0.53.0"
}

repositories { mavenCentral() }

dependencies {
    subprojects.forEach {
        dokka(it)
    }
}