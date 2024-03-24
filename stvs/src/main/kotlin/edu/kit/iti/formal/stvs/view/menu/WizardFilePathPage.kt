package edu.kit.iti.formal.stvs.view.menu

import de.jensd.fx.glyphs.GlyphsDude
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon
import edu.kit.iti.formal.stvs.view.common.ActualHyperLink
import edu.kit.iti.formal.stvs.view.common.FileSelectionField
import javafx.beans.Observable
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import javafx.beans.property.StringProperty
import javafx.scene.Node
import javafx.scene.control.Label
import javafx.scene.layout.HBox
import java.io.File

/**
 * Created by leonk on 22.03.2017.
 */
class WizardFilePathPage(title: String, description: String?, filePath: StringProperty?) : WizardPage(title) {
    private val filePathField = FileSelectionField()
    private val valid: BooleanProperty = SimpleBooleanProperty()
    private val notValidContainer = HBox(20.0)

    init {
        val notValidIcon: Node = GlyphsDude.createIcon(FontAwesomeIcon.EXCLAMATION_TRIANGLE)
        notValidContainer.children.addAll(
            notValidIcon,
            Label("Something is wrong with this path. Not all features of STVS will work as expected!")
        )
        notValidContainer.visibleProperty().bind(valid.not())
        filePathField.textField.textProperty().addListener { observable: Observable -> this.validator(observable) }
        validator(filePathField.textField.textProperty())

        children.addAll(Label(description), filePathField, notValidContainer)
        filePathField.textField.textProperty().bindBidirectional(filePath)
    }

    constructor(
        title: String, description: String?, filePath: StringProperty?,
        downloadLink: String
    ) : this(title, description, filePath) {
        children.addAll(
            Label("Download the dependency from:"),
            ActualHyperLink(downloadLink, downloadLink)
        )
    }

    private fun validator(observable: Observable) {
        val path = filePathField.textField.textProperty().get()
        if (path != null && File(path).canRead()) {
            valid.value = true
        } else {
            valid.value = false
        }
    }

    fun isValid(): Boolean {
        return valid.get()
    }

    fun validProperty(): BooleanProperty {
        return valid
    }
}
