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
package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.view.Controller
import javafx.application.Platform
import javafx.beans.property.DoubleProperty
import javafx.beans.property.SimpleDoubleProperty
import javafx.event.EventHandler
import javafx.scene.Node
import javafx.scene.input.MouseEvent
import javafx.scene.layout.AnchorPane

/**
 * Controller for [VerticalResizeContainerView].
 *
 * @author Leon Kaucher
 */
class VerticalResizeContainerController(wrap: Node?) : Controller {
    override var view: VerticalResizeContainerView = VerticalResizeContainerView()
    private val mouseYStart: DoubleProperty = SimpleDoubleProperty(0.0)
    private val cacheSize: DoubleProperty = SimpleDoubleProperty(0.0)

    /**
     * Creates a simple wrapper that enables one to vertically resize the given Node.
     *
     * @param wrap Node that should be wrapped
     */
    init {
        view.content.children.add(wrap)
        AnchorPane.setLeftAnchor(wrap, 0.0)
        AnchorPane.setRightAnchor(wrap, 0.0)
        AnchorPane.setTopAnchor(wrap, 0.0)
        AnchorPane.setBottomAnchor(wrap, 0.0)
        view.dragLine.onMousePressed = EventHandler { event: MouseEvent ->
            mouseYStart.value = event.screenY
            cacheSize.value = view.content.height
            view.contentContainer.prefHeight = view.content.height
        }
        view.dragLine.onMouseDragged = EventHandler { event: MouseEvent ->
            val newSize = cacheSize.get() + (event.screenY - mouseYStart.get())
            if (newSize >= cacheSize.get()) {
                view.contentContainer.prefHeight = newSize
            }
            view.content.prefHeight = newSize
        }
        view.dragLine.onMouseReleased = EventHandler { event: MouseEvent ->
            println("release")
            val newSize = cacheSize.get() + (event.screenY - mouseYStart.get())
            view.contentContainer.prefHeight = newSize
            view.content.prefHeight = newSize
            Platform.runLater {
                view.parent.parent.parent.parent.parent
                    .parent.requestLayout()
            }
        }
    }
}