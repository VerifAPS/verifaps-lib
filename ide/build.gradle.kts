plugins {
    id("kotlin-convention")
    id("application")
    id("org.openjfx.javafxplugin") version "0.1.0"
}


javafx {
    version = "21"
    modules = listOf("javafx.controls", "javafx.controls", "javafx.fxml", "javafx.graphics")
}

application {
    mainClass = "edu.kit.iti.formal.automation.fx.Main"
}

dependencies {
    implementation(project(":symbex"))
    implementation(project(":geteta"))
    implementation(project(":aps-rvt"))
    implementation(project(":run"))
    implementation(project(":fxutils"))
    implementation(libs.clickt)
}
