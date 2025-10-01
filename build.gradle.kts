plugins {
    id("dokka-convention")
    id("org.sonarqube") version "6.3.1.5724"
    id("com.github.ben-manes.versions") version "0.53.0"
}

repositories { mavenCentral() }

// configuration for subproject-A only.
tasks.dokkaHtmlMultiModule {
    // moduleName.set("verifaps")
}