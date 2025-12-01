plugins {
    id("dokka-convention")
    id("org.sonarqube") version "7.1.0.6387"
    id("com.github.ben-manes.versions") version "0.53.0"
}

repositories { mavenCentral() }

// configuration for subproject-A only.
tasks.dokkaHtmlMultiModule {
    // moduleName.set("verifaps")
}