package edu.kit.iti.formal.automation.fx

import javafx.beans.property.SimpleStringProperty
import javafx.scene.Group
import javafx.scene.layout.Pane
import javafx.scene.paint.Color
import javafx.scene.shape.Rectangle
import javafx.scene.text.Text
import tornadofx.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/28/21)
 */
class ContractAutomataEditor : View() {
    override val root = Pane()
    val nodes = arrayListOf<State>()

    init {
        nodes.add()
    }
}

class State : Group() {
    val border = Rectangle(0.0, 0.0, 100.0, 200.0)
    val xProperty = border.xProperty()
    val yProperty = border.xProperty()
    val widthProperty = border.widthProperty()
    val heightProperty = border.heightProperty()

    val text = Text()
    val titleProperty = text.textProperty()
    var title by titleProperty

    init {
        border.fill = null
        border.arcHeight = 5.0;
        border.arcWidth = 5.0;
        border.stroke = Color.BLACK

        children.add(border)
        children.add(text)
    }
}
