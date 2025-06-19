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

import edu.kit.iti.formal.stvs.StvsApplication
import javafx.application.Preloader
import javafx.geometry.Insets
import javafx.scene.Scene
import javafx.scene.control.Label
import javafx.scene.image.Image
import javafx.scene.image.ImageView
import javafx.scene.layout.Background
import javafx.scene.layout.BorderPane
import javafx.scene.layout.Region
import javafx.scene.layout.VBox
import javafx.scene.paint.Color
import javafx.stage.Screen
import javafx.stage.Stage
import javafx.stage.StageStyle

/**
 * Created by csicar on 21.03.17.
 */
class StvsPreloader : Preloader() {
    private var stage: Stage? = null
    private var splashImage: Image? = null

    override fun init() {
        splashImage = Image(StvsApplication::class.java.getResourceAsStream("logo.png"))
    }

    override fun start(stage: Stage) {
        this.stage = stage

        stage.initStyle(StageStyle.TRANSPARENT)

        val box = VBox(20.0)
        box.maxWidth = Region.USE_PREF_SIZE
        box.maxHeight = Region.USE_PREF_SIZE
        box.background = Background.EMPTY
        val style = "-fx-background-color: rgba(255, 255, 255, 0.5);"
        box.style = style

        box.padding = Insets(50.0)
        val root = BorderPane(box)
        root.style = style
        root.background = Background.EMPTY
        val scene = Scene(root)
        scene.fill = Color.TRANSPARENT
        stage.scene = scene

        val splashView = ImageView(splashImage)
        box.children.addAll(splashView, Label("ST Verification Studio is loading.."))
        stage.show()
        val primScreenBounds = Screen.getPrimary().visualBounds
        stage.x = (primScreenBounds.width - stage.width) / 2
        stage.y = (primScreenBounds.height - stage.height) / 2
    }

    override fun handleStateChangeNotification(evt: StateChangeNotification) {
        if (evt.type == StateChangeNotification.Type.BEFORE_START) {
            try {
                Thread.sleep(1000)
            } catch (e: InterruptedException) {
                e.printStackTrace()
            }
            stage!!.hide()
        }
    }
}