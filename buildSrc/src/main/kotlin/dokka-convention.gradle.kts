import org.jetbrains.dokka.gradle.DokkaTaskPartial
import org.jetbrains.dokka.base.DokkaBase
import org.jetbrains.dokka.gradle.DokkaTask
import org.jetbrains.dokka.base.DokkaBaseConfiguration
import java.net.URI

plugins {
    id("org.jetbrains.dokka")
}

dependencies {
    dokkaPlugin("org.jetbrains.dokka:mathjax-plugin:2.0.0")
    dokkaPlugin("com.glureau:html-mermaid-dokka-plugin:0.6.0")
}

tasks.withType<DokkaTask>().configureEach {
    pluginConfiguration<DokkaBase, DokkaBaseConfiguration> {
        customAssets = listOf(rootDir.resolve("gradle/dokkaAssets"), rootDir.resolve("gradle/dokkaAssets/screenshot.png"))
        // customStyleSheets = listOf(file("my-styles.css"))
        footerMessage = "(c) 2014-2025 Alexander Weigl"
        // separateInheritedMembers = false
        // templatesDir = file("dokka/templates")
        // mergeImplicitExpectActualDeclarations = false
    }
}

// configure all format tasks at once
tasks.withType<DokkaTaskPartial>().configureEach {
    dokkaSourceSets {
        named("main") {
            // used as project name in the header
            // moduleName.set("Dokka Gradle Example")

            // contains descriptions for the module and the packages
            includes.from(rootDir.resolve("MODULES.md"))
            // projectDir.resolve("README.md"))

            sourceLink {
                localDirectory.set(file("src/main/kotlin"))
                remoteUrl.set(URI("https://github.com/verifaps/verifaps-lib/blob/").toURL())
                remoteLineSuffix.set("#L")
            }
        }
    }
}