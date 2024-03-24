package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.StvsApplication
import javafx.scene.control.Label
import javafx.scene.image.Image
import javafx.scene.image.ImageView
import javafx.scene.layout.HBox

/**
 * Created by leonk on 23.03.2017.
 */
class WizardWelcomePage : WizardPage("Welcome!") {
    init {
        val introBox = HBox(20.0)
        val logo =
            ImageView(Image(StvsApplication::class.java.getResourceAsStream("logo.png")))
        val intro = Label(
            "Thank you for choosing STVerificationStudio!\nThis wizard will guide you through the installation of all third party dependencies."
        )
        introBox.children.addAll(logo, intro)
        children.add(introBox)
    }
}
