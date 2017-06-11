package edu.kit.iti.formal.automation.rvt.gui

import javafx.scene.layout.BorderPane
import tornadofx.View

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.06.17)
 */
class RVTApp : tornadofx.App(RVTGuiMain::class, RVTStylesheet::class)

class RVTGuiMain : View() {
    override val root: BorderPane by fxml()
}

class RVTStylesheet : tornadofx.Stylesheet() {
    init {

    }
}
