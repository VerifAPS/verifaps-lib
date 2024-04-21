package edu.kit.iti.formal.stvs.view.common

import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.Hyperlink

/**
 * Created by csicar on 16.03.17.
 */
class ActualHyperLink(name: String, url: String) : Hyperlink(name) {
    init {
        this.onAction = EventHandler { _: ActionEvent? -> HostServiceSingleton.instance?.showDocument(url) }
    }
}
