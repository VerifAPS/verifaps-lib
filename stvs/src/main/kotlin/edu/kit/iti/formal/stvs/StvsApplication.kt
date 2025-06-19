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
package edu.kit.iti.formal.stvs

import edu.kit.iti.formal.stvs.StvsVersion.windowTitle
import edu.kit.iti.formal.stvs.view.StvsMainScene
import edu.kit.iti.formal.stvs.view.common.HostServiceSingleton
import javafx.application.Application
import javafx.application.Application.launch
import javafx.application.Platform
import javafx.scene.Node
import javafx.scene.control.TitledPane
import javafx.scene.image.Image
import javafx.scene.input.MouseEvent
import javafx.stage.Stage
import jfxtras.styles.jmetro.JMetro
import jfxtras.styles.jmetro.Style
import org.fxmisc.cssfx.CSSFX
import java.util.*
import kotlin.system.exitProcess

/**
 * The entry point to ST Verification Studio.
 *
 * @author Leon Kaucher
 */
class StvsApplication : Application() {
    var mainScene = StvsMainScene()
    var primaryStage: Stage? = null

    override fun start(primaryStage: Stage) {
        HostServiceSingleton.instance = hostServices
        this.primaryStage = Stage()
        Platform.setImplicitExit(true)
        primaryStage.title = windowTitle
        primaryStage.isMaximized = mainScene.shouldBeMaximizedProperty().get()

        mainScene.shouldBeMaximizedProperty().bind(primaryStage.maximizedProperty())

        mainScene.scene.stylesheets.add(
            StvsApplication::class.java.getResource("normal.css")!!.toExternalForm(),
        )

        val metro = JMetro(Style.LIGHT)
        metro.scene = mainScene.scene
        metro.reApplyTheme()

        CSSFX.start(mainScene.scene)

        // Debugger snippet for finding the styleclasses for the node under cursor.
        mainScene.scene.addEventFilter(MouseEvent.MOUSE_MOVED) { mouseEvent: MouseEvent ->
            if (mouseEvent.isAltDown && mouseEvent.isControlDown) {
                val node = mouseEvent.target as Node
                val classes = node.styleClass
                println("Classes of " + node.javaClass.simpleName + " are " + classes)
                println("Style of " + node.javaClass.simpleName + ": " + node.style)

                println((node as TitledPane).alignment)
                println(node.textAlignment)
            }
        }

        if (System.getProperty("presentation", "false") == "true") {
            mainScene.scene.stylesheets.add(
                StvsApplication::class.java.getResource("presentation.css")!!.toExternalForm(),
            )
        }

        Platform.runLater {
            primaryStage.icons.addAll(
                Image(StvsApplication::class.java.getResourceAsStream("logo_large.png")),
                Image(StvsApplication::class.java.getResourceAsStream("logo.png")),
            )

            this.mainScene = StvsMainScene()
            primaryStage.scene = mainScene.scene
        }

        primaryStage.show()
    }

    override fun stop() {
        mainScene.onClose()
        primaryStage!!.hide()
        exitProcess(0)
    }
}

object Main {
    /**
     * Launch the application.
     *
     * @param args The command-line arguments passed to the application
     */
    @JvmStatic
    fun main(args: Array<String>) {
        Locale.setDefault(Locale.ENGLISH)
        launch(StvsApplication::class.java, *args)
    }
}