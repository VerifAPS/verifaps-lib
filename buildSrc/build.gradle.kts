import org.gradle.kotlin.dsl.plugins

plugins {
    `kotlin-dsl`
}

repositories {
    mavenCentral()
    gradlePluginPortal()
}

kotlin {
    jvmToolchain(23)
}

dependencies {
    implementation("org.jetbrains.dokka:dokka-gradle-plugin:2.0.0")
    implementation("org.jetbrains.dokka:dokka-base:2.0.0")
    implementation("com.diffplug.spotless:com.diffplug.spotless.gradle.plugin:7.0.4")
    implementation(libs.kotlinGradlePlugin)
}

