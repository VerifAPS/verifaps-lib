import org.jetbrains.dokka.gradle.DokkaTaskPartial

plugins {
    id("dokka-convention")
    id("org.sonarqube") version "6.1.0.5360"
    id("com.github.ben-manes.versions") version "0.52.0"
}

repositories { mavenCentral() }

// configuration for subproject-A only.
tasks.dokkaHtmlMultiModule {
    //moduleName.set("verifaps")
}