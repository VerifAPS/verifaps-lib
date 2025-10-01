plugins {
    id("kotlin-convention")
    id("org.openjfx.javafxplugin") version "0.1.0"
}

javafx {
    version = "22"
    modules = listOf("javafx.controls")
}

dependencies {
    for (module in listOf("javafx-controls", "javafx-fxml", "javafx-graphics", "javafx-web")) {
        for (classifier in listOf("win", "linux", "mac")) {
            api("org.openjfx:$module:22:$classifier")
        }
    }

    api("com.pixelduke:fxribbon:1.2.2")
    api("no.tornado:tornadofx:1.7.20") {
        exclude("org.jetbrains.kotlin:kotlin-stdlib")
    }
    api("com.miglayout:miglayout-javafx:11.4.2")
    api("org.fxmisc.richtext:richtextfx:0.11.6")
    api("org.kordamp.ikonli:ikonli-fontawesome5-pack:12.4.0")
    api("org.kordamp.ikonli:ikonli-materialdesign2-pack:12.4.0")
    api("org.kordamp.ikonli:ikonli-javafx:12.4.0")
    api("com.pixelduke:fxribbon:1.2.2")
    api("org.jfxtras:jmetro:11.6.16")
    api("org.controlsfx:controlsfx:11.2.2")
}