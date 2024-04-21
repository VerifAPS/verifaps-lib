plugins {
    id("org.openjfx.javafxplugin") version "0.1.0"
}

javafx {
    version = "21"
    modules = listOf("javafx.controls")
}

dependencies {
    api("com.pixelduke:fxribbon:1.2.2")
    api("no.tornado:tornadofx:1.7.20")
    api("com.miglayout:miglayout-javafx:11.3")
    api("org.fxmisc.richtext:richtextfx:0.11.2")
    api("org.kordamp.ikonli:ikonli-fontawesome5-pack:12.3.1")
    api("org.kordamp.ikonli:ikonli-materialdesign2-pack:12.3.1")
    api("org.kordamp.ikonli:ikonli-javafx:12.3.1")
    api("com.pixelduke:fxribbon:1.2.2")
    api("org.jfxtras:jmetro:11.6.15")
    api("org.controlsfx:controlsfx:8.40.13")
}