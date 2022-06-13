package edu.kit.iti.formal.automation.fx

import edu.kit.iti.formal.automation.testtables.model.TableNode
import javafx.scene.control.TreeTableView
import tornadofx.View
import tornadofx.label

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/21/21)
 */
class Geteta : View("Geteta") {
    override val root = label("Test") { }
}

class Reteta : View("Reteta") {
    override val root = label("Test") { }
}


class TTPreview : View("Preview") {
    override val root = TreeTableView<TableNode>()
    init {

    }
}