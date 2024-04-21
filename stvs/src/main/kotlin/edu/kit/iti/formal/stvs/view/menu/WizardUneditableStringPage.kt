package edu.kit.iti.formal.stvs.view.menu

import javafx.beans.property.StringProperty
import javafx.scene.control.Label
import javafx.scene.control.TextField
import javafx.scene.text.TextAlignment

/**
 * Created by leonk on 23.03.2017.
 */
class WizardUneditableStringPage(
    title: String, description: String?,
    uneditableText: StringProperty
) : WizardPage(title) {
    init {
        val uneditableTextField = TextField()
        uneditableTextField.textProperty().bind(uneditableText)
        val descriptionLabel = Label(description)
        descriptionLabel.isWrapText = true
        descriptionLabel.textAlignment = TextAlignment.JUSTIFY
        children.addAll(descriptionLabel, uneditableTextField)
        uneditableTextField.isDisable = true
    }
}
