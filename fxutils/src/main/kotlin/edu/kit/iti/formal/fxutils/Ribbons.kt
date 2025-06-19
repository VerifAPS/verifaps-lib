/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 *
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
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
    graphic: Node? = null,
    event: () -> Unit,
): Button {
    val item = buildItem(ikon, ikof, graphic, key, name, event)
    this.nodes.add(item)
    return item
}

fun Column.item(
    name: String,
    key: String? = null,
    ikon: String? = null,
    ikof: Ikon? = null,
    graphic: Node? = null,
    event: () -> Unit,
): Button {
    val item = buildItem(ikon, ikof, graphic, key, name, event)
    this.children.add(item)
    return item
}

private fun buildItem(ikon: String?, ikof: Ikon?, graphic: Node? = null, key: String?, name: String, event: () -> Unit): Button {
    val icon = ikon?.let { ref ->
        FontIcon(ref)
    } ?: ikof?.let { FontIcon(ikof) } ?: graphic

    val k = key?.let { KeyCombination.keyCombination(it) }
    val item = Button(name, icon).also {
        // it.accelerator = k
        it.graphic = icon
        it.onAction = EventHandler { _ -> event() }
    }
    return item
}

fun RibbonGroup.column(op: Column.() -> Unit) = Column().also {
    op(it)
    this.nodes.add(it)
}
