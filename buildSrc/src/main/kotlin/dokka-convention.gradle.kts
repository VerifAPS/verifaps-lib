import gradle.kotlin.dsl.accessors._ae0e2e0f59d526dd61b4865f6e032691.dokkaPublications
import java.net.URI

plugins {
    id("org.jetbrains.dokka")
}

dependencies {
    dokkaPlugin("org.jetbrains.dokka:mathjax-plugin:2.0.0")
    dokkaPlugin("com.glureau:html-mermaid-dokka-plugin:0.6.0")
}

dokka {
    moduleName.set("verifaps/${project.name}")
    dokkaPublications.html {
        suppressInheritedMembers.set(true)
        failOnWarning.set(false)
    }

    dokkaPublications.html {
        // outputDirectory.set(rootDir.resolve("docs/api/0.x"))
    }

    dokkaSourceSets {
        configureEach {
            // Or source set name, for single-platform the default source sets are `main` and `test`
            // includes.from("$rootDir/MODULES.md")
            sourceLink {
                localDirectory.set(file("src/main/kotlin"))
                remoteUrl.set(URI("https://github.com/verifaps/verifaps-lib/blob/"))
                remoteLineSuffix.set("#L")
            }
        }
    }
    pluginsConfiguration.html {
        customAssets.from(rootDir.resolve("gradle/dokkaAssets/screenshot.png"))
        customAssets.from(rootDir.resolve("gradle/dokkaAssets"))
        footerMessage = "(c) 2014-2026 Alexander Weigl"
    }
}