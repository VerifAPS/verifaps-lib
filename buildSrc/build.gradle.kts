import org.gradle.kotlin.dsl.plugins

plugins {
    `kotlin-dsl`
}

repositories {
    mavenCentral()
    gradlePluginPortal()
}

kotlin {
    jvmToolchain(21)
}

dependencies {
    // implementation("org.tukaani:xz:1.10")
    implementation("org.jetbrains.dokka:dokka-gradle-plugin:2.1.0")
    implementation("org.jetbrains.dokka:dokka-base:2.1.0")
    implementation("com.diffplug.spotless:com.diffplug.spotless.gradle.plugin:7.0.4")
    implementation(libs.kotlinGradlePlugin)
}