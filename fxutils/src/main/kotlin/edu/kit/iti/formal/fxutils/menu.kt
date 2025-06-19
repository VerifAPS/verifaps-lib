package edu.kit.iti.formal.fxutils

import javafx.event.EventHandler
import javafx.scene.control.Menu
import javafx.scene.input.KeyCombination
import org.kordamp.ikonli.javafx.FontIcon
import tornadofx.item

fun Menu.item(name: String, key: String?, ikon: String? = null, event: () -> Unit) {
    val icon = ikon?.let { ref -> FontIcon(ref) }
    item(name, key?.let { KeyCombination.keyCombination(it) }, icon) {
        onAction = EventHandler { _ -> event() }
    }
}