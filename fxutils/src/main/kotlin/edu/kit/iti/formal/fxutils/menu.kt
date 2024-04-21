package edu.kit.iti.formal.fxutils

import tornadofx.*
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.input.KeyCombination
import org.kordamp.ikonli.javafx.*

fun Menu.item(name: String, key: String?, ikon: String? = null, event: () -> Unit) {
    val icon = ikon?.let { ref ->
        val resolver = IkonResolver.getInstance()
        resolver.resolve(ref).resolve(ref)?.let { FontIcon(it) }
    }
    item(name, key?.let { KeyCombination.keyCombination(it) }, icon) {
        onAction = EventHandler { _ -> event() }
    }
}