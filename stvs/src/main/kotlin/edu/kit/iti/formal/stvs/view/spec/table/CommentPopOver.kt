package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.view.spec.Lockable
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import javafx.geometry.Insets
import javafx.scene.control.Button
import javafx.scene.control.ButtonBar
import javafx.scene.control.TextArea
import javafx.scene.layout.VBox
import org.controlsfx.control.PopOver
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

class CommentPopOver : PopOver(), Lockable {
    override val editableProperty: BooleanProperty = SimpleBooleanProperty(true)

    val textArea: TextArea = TextArea()

    private val buttonBar = ButtonBar()

    val saveButton: Button = Button(null, FontIcon(FontAwesomeSolid.SAVE))

    init {
        buttonBar.buttons.addAll(saveButton)
        val content = VBox(textArea, buttonBar)
        content.padding = Insets(5.0)
        this.title = "Edit Comment"
        this.contentNode = content
        textArea.editableProperty().bind(editableProperty)
    }
}
