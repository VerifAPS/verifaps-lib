plugins {
    id("dokka-convention")
    id("org.sonarqube") version "7.0.1.6134"
    id("com.github.ben-manes.versions") version "0.53.0"
}

repositories { mavenCentral() }

// configuration for subproject-A only.
tasks.dokkaHtmlMultiModule {
    // moduleName.set("verifaps")
}