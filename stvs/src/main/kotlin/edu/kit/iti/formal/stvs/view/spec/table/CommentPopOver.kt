package edu.kit.iti.formal.stvs.view.spec.table

import de.jensd.fx.glyphs.GlyphsDude
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon
import edu.kit.iti.formal.stvs.view.spec.Lockable
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import javafx.geometry.Insets
import javafx.scene.control.Button
import javafx.scene.control.ButtonBar
import javafx.scene.control.TextArea
import javafx.scene.layout.VBox
import org.controlsfx.control.PopOver

class CommentPopOver : PopOver(), Lockable {
    override val editableProperty: BooleanProperty = SimpleBooleanProperty(true)

    val textArea: TextArea = TextArea()

    private val buttonBar = ButtonBar()

    val saveButton: Button = GlyphsDude.createIconButton(FontAwesomeIcon.SAVE)

    init {
        buttonBar.buttons.addAll(saveButton)
        val content = VBox(textArea, buttonBar)
        content.padding = Insets(5.0)
        this.title = "Edit Comment"
        this.contentNode = content
        textArea.editableProperty().bind(editableProperty)
    }
}
