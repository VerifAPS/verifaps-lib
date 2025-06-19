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

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.scene.layout.AnchorPane
import javafx.scene.layout.VBox
import javafx.scene.paint.Color
import javafx.scene.shape.Rectangle

/**
 * Creates a Container for resizing through a horizontal bar.
 *
 * @author Leon Kaucher
 */
class VerticalResizeContainerView : AnchorPane() {
    val container: VBox = VBox()
    val content: AnchorPane = AnchorPane()
    val contentContainer: VBox = VBox()
    val dragLine: Rectangle = Rectangle(10.0, 10.0, Color.BEIGE)

    /**
     * Creates an instance of this container class.
     */
    init {
        children.add(container)
        container.children.addAll(contentContainer)
        contentContainer.children.addAll(content, dragLine)
        setLeftAnchor(container, 0.0)
        setRightAnchor(container, 0.0)
        setTopAnchor(container, 0.0)
        dragLine.widthProperty().bind(container.widthProperty())
        // AnchorPane.setBottomAnchor(dragLine, 0.0);
        ViewUtils.setupView(this, "resizeContainer.css")

        styleClass.add("resizeContainer")
        dragLine.styleClass.add("dragLine")
    }
}