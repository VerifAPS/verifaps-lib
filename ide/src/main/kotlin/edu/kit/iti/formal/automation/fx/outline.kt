package edu.kit.iti.formal.automation.fx

import javafx.scene.Parent
import javafx.scene.control.TreeView
import tornadofx.View

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/21/21)
 */
class FileOutline : View("Outline") {
    val outlineTree = TreeView<Any>()
    override val root: Parent
        get() = outlineTree
}
