import org.gradle.api.tasks.testing.logging.TestLogEvent

plugins {
    `maven-publish`
    `java-library`
    jacoco
    kotlin("jvm")
    id("dokka-convention")
}

repositories {
    mavenCentral()
}

dependencies {
    val libs = versionCatalogs.named("libs")
    implementation(libs.findLibrary("kotlinxCoroutines").get())
    implementation(libs.findBundle("logging").get())
    testImplementation(libs.findBundle("testing").get())

    implementation(kotlin("stdlib-jdk8"))
    implementation(kotlin("reflect"))
    //implementation( "org.jetbrains", name: "annotations", version: "26.0.2"

    testImplementation("com.google.truth:truth:1.4.4")

    testImplementation("org.jetbrains.kotlin:kotlin-test-junit:2.1.0")
    testImplementation(project(":utils-test"))
}


kotlin {
    // Use a specific Java version to make it easier to work in different environments.
    jvmToolchain(21)
}

tasks.withType<Test>().configureEach {
    // Configure all test Gradle tasks to use JUnitPlatform.
    useJUnitPlatform()

    // Log information about all test results, not only the failed ones.
    testLogging {
        events(
            TestLogEvent.FAILED,
            //TestLogEvent.PASSED,
            //TestLogEvent.SKIPPED
        )
    }
}

jacoco {
    toolVersion = "0.8.12"
}

tasks.jacocoTestReport {
    reports {
        xml.required = true
        html.required = true
    }
}

tasks.register<Jar>("testJar") {
    archiveClassifier.set("tests")
    //from sourceSets . test . output
    //        from sourceSets . test . resources
}

tasks.withType<JavaCompile>().configureEach {
    options.encoding = "UTF-8"
}


tasks.getByName<Jar>("jar") {
    manifest {
        attributes(
            "Implementation-Title" to project.name,
            "Implementation-Version" to version,
            "Description" to description,
        )
    }
}

val sourcesJar = tasks.register<Jar>("sourcesJar") {
    from(sourceSets.main)//.allJava
    archiveClassifier = "sources"
}

val javadocJar by tasks.register<Jar>("javadocJar") {
    from(tasks.getByName("javadoc"))
    archiveClassifier = "javadoc"
}

publishing {
    repositories {
        maven {
            name = "GitHubPackages"
            url = uri("https://maven.pkg.github.com/verifaps/verifaps-lib")
            credentials {
                //username = project.findProperty("gpr.user") ?: System.getenv("USERNAME")
                //password = project.findProperty("gpr.key") ?: System.getenv("PASSWORD")
            }
        }
    }
    publications {
        create<MavenPublication>("gpr") {
            //TODO from(components.java)
            artifact(sourcesJar)
            artifact(javadocJar)
            pom {
                name = project.name
                description = project.description
                url = "https://formal.iti.kit.edu/verifaps"
                licenses {
                    license {
                        name = "Gnu Public License, Version 3.0"
                        url = "https://www.gnu.org/licenses/gpl-3.0.html"
                    }
                }
                developers {
                    developer {
                        id = "weigl"
                        name = "Alexander Weigl"
                        email = "weigl@kit.edu"
                    }
                }
                scm {
                    connection = "https://github.com/verifaps/verifaps-lib.git"
                    url = "https://github.com/verifaps/verifaps-lib.git"
                }
            }
        }
    }
}

if (project.plugins.hasPlugin("antlr")) {
    dependencies {
        val libs = versionCatalogs.named("libs")
        implementation(libs.findLibrary("antlrRuntime").get())
        val antlr = configurations.getByName("antlr")
        antlr(libs.findLibrary("antlr").get())
    }


    val ggs = tasks["generateGrammarSource"]
    val gtgs = tasks["generateTestGrammarSource"]

    tasks["compileJava"].dependsOn(ggs)
    tasks["compileKotlin"].dependsOn(ggs)
    tasks["compileTestKotlin"].dependsOn(gtgs)
    tasks["compileTestJava"].dependsOn(gtgs)
}
