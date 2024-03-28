package edu.kit.iti.formal.stvs.view.menu

import javafx.scene.Node
import javafx.scene.layout.VBox

/**
 * Created by leonk on 22.03.2017.
 */
open class WizardPage(var title: String) : VBox() {
    init {
        spacing = 20.0
    }

    constructor(title: String, content: Node?) : this(title) {
        children.setAll(content)
    }
}
