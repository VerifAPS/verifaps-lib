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
package edu.kit.iti.formal.stvs.view

import javafx.application.Application
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.control.SplitPane
import javafx.stage.Stage
import java.util.function.Supplier

/**
 * Created by Lukas on 20.01.2017.
 */
class JavaFxTest : Application() {
    @Throws(Exception::class)
    override fun start(primaryStage: Stage) {
        primaryStage.scene = toBeViewed!!.get()
        primaryStage.show()
    }

    companion object {
        private var toBeViewed: Supplier<Scene?>? = null

        @JvmStatic
        fun main(args: Array<String>) {
            launch(*args)
        }

        fun setToBeViewed(toBeViewed: Supplier<Scene?>?) {
            Companion.toBeViewed = toBeViewed
        }

        fun runView(toBeViewed: Supplier<Scene?>?) {
            setToBeViewed(toBeViewed)
            launch(JavaFxTest::class.java)
        }

        fun runSplitView(supplierOfViews: Supplier<List<Node?>>) {
            runView {
                val pane = SplitPane()
                pane.items.addAll(supplierOfViews.get())

                val scene = Scene(pane, 800.0, 600.0)

                scene.stylesheets.add(JavaFxTest::class.java.getResource("style.css")!!.toExternalForm())
                scene
            }
        }
    }
}