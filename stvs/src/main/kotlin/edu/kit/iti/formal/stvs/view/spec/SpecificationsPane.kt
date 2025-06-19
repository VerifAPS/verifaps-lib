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
package edu.kit.iti.formal.stvs.view.spec

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.Button
import javafx.scene.control.Tab
import javafx.scene.control.TabPane
import javafx.scene.layout.AnchorPane

/**
 * This Pane displays a collection of specifications as tabs.
 *
 * @author Carsten Csiky
 */
class SpecificationsPane : AnchorPane() {
    val tabPane: TabPane = TabPane()
    val addButton: Button = Button("+")

    /**
     * Creates an empty instance.
     */
    init {
        ViewUtils.setupClass(this)

        setTopAnchor(tabPane, 0.0)
        setLeftAnchor(tabPane, 0.0)
        setRightAnchor(tabPane, 0.0)
        setBottomAnchor(tabPane, 0.0)
        setTopAnchor(addButton, 5.0)
        setRightAnchor(addButton, 5.0)

        children.addAll(tabPane, addButton)
    }

    val tabs: ObservableList<Tab?>
        get() = tabPane.tabs

    /**
     * Defines what should be invoked if a tab is added.
     * @param listener method to invoke
     */
    fun onTabAdded(listener: Runnable) {
        addButton.onAction = EventHandler { actionEvent: ActionEvent? ->
            listener.run()
        }
    }
}