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

import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.application.Application
import javafx.scene.Scene
import javafx.scene.layout.Pane
import javafx.scene.layout.Priority
import javafx.scene.layout.VBox
import javafx.scene.paint.Color
import javafx.scene.shape.Rectangle
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import java.util.function.Supplier

/**
 * Created by leonk on 10.02.2017.
 */
@Tag("demo")
class VerticalResizeContainerControllerDemo {
    @Test
    fun javaFxTest() {
        JavaFxTest.Companion.setToBeViewed(Supplier<Scene?> { this.simpleScene() })
        Application.launch(JavaFxTest::class.java)
    }

    private fun simpleScene(): Scene? {
        try {
            val root = VBox()
            val pane = Pane()
            val rectangle = Rectangle(100.0, 100.0, Color.AQUA)
            pane.children.addAll(rectangle)
            val controller = VerticalResizeContainerController(pane)
            root.children.addAll(controller.view)
            VBox.setVgrow(controller.view, Priority.ALWAYS)
            val scene = Scene(root, 800.0, 600.0)
            return scene
        } catch (e: Exception) {
            e.printStackTrace()
            return null
        }
    }
}