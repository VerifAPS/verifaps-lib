package edu.kit.iti.formal.fxutils

import com.pixelduke.control.Ribbon
import com.pixelduke.control.ribbon.Column
import com.pixelduke.control.ribbon.RibbonGroup
import com.pixelduke.control.ribbon.RibbonTab
import javafx.event.EventHandler
import javafx.event.EventTarget
import javafx.scene.Node
import javafx.scene.control.Button
import javafx.scene.input.KeyCombination
import org.kordamp.ikonli.Ikon
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.javafx.IkonResolver
import tornadofx.attachTo


fun EventTarget.ribbon(op: Ribbon.() -> Unit = {}) = Ribbon().attachTo(this, op)

fun ribbon(op: Ribbon.() -> Unit = {}) = Ribbon().also(op)

fun Ribbon.tab(title: String = "", op: RibbonTab.() -> Unit = {}) = RibbonTab(title).also {
    op(it)
    this.tabs.add(it)
}

fun RibbonTab.group(title: String = "", op: RibbonGroup.() -> Unit = {}) = RibbonGroup().also {
    it.title = title
    op(it)
    this.ribbonGroups.add(it)
}

fun RibbonGroup.item(
    name: String,
    key: String? = null,
    ikon: String? = null,
    ikof: Ikon? = null,
    graphic: Node?=null,
    event: () -> Unit
): Button {
    val item = buildItem(ikon, ikof, graphic,key, name, event)
    this.nodes.add(item)
    return item
}

fun Column.item(
    name: String,
    key: String? = null,
    ikon: String? = null,
    ikof: Ikon? = null,
    graphic: Node?=null,
    event: () -> Unit
): Button {
    val item = buildItem(ikon, ikof, graphic, key, name, event)
    this.children.add(item)
    return item
}

private val resolver = IkonResolver.getInstance()

private fun buildItem(ikon: String?, ikof: Ikon?, graphic: Node?=null, key: String?, name: String, event: () -> Unit): Button {
    val icon = ikon?.let { ref ->
        resolver.resolve(ref).resolve(ref)?.let { FontIcon(it) }
    } ?: ikof?.let { FontIcon(ikof) } ?: graphic

    val k = key?.let { KeyCombination.keyCombination(it) }
    val item = Button(name, icon).also {
        //it.accelerator = k
        it.graphic = icon
        it.onAction = EventHandler { _ -> event() }
    }
    return item
}

fun RibbonGroup.column(op: Column.() -> Unit) = Column().also {
    op(it)
    this.nodes.add(it)
}
