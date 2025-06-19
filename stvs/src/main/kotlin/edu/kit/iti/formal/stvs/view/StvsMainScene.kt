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

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import edu.kit.iti.formal.stvs.view.menu.StvsToolbarController
import javafx.application.Platform
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.scene.Scene
import javafx.scene.control.Alert
import javafx.scene.layout.BorderPane
import tornadofx.getValue
import tornadofx.setValue
import java.io.IOException

/**
 * Main Scene that holds all visible nodes of the program.
 *
 * @author Lukas Fritsch
 */
class StvsMainScene(rootModel: StvsRootModel = StvsRootModel()) {
    private val rootModelProperty = SimpleObjectProperty(rootModel)
    var rootModel: StvsRootModel by rootModelProperty

    var rootController: StvsRootController = StvsRootController(rootModelProperty.get())

    val menuBarController = StvsToolbarController(rootModelProperty)

    val scene: Scene

    /**
     * Creates an instance from a root model.
     * @param rootModel Model that should be represented by this instance.
     */
    init {
        rootModelProperty.get().globalConfig.setAll(GlobalConfig.autoloadConfig())
        rootModelProperty.get().history.setAll(History.autoloadHistory())

        rootModelProperty.addListener { obs, oldModel, rootModel -> this.rootModelChanged(rootModel) }

        this.scene = Scene(
            createVBox(),
            rootModel.globalConfig.windowWidth.toDouble(),
            rootModel.globalConfig.windowHeight.toDouble(),
        )

        rootModel.globalConfig.windowWidthProperty.bind(scene.widthProperty())
        rootModel.globalConfig.windowHeightProperty.bind(scene.heightProperty())

        Platform.runLater {
            this.rootModel = StvsRootModel.autoloadSession()
        }
    }

    private fun createVBox() = BorderPane(rootController.view, menuBarController.view, null, null, null)

    private fun rootModelChanged(rootModel: StvsRootModel) {
        this.rootController = StvsRootController(rootModel)
        scene.root = createVBox()
    }

    /**
     * Code that should be executed before the scene is destroyed on exit.
     */
    fun onClose() {
        val stvsRootModel: StvsRootModel? = rootModelProperty.get()
        if (stvsRootModel != null) {
            try {
                stvsRootModel.globalConfig.autosaveConfig()
                stvsRootModel.history.autosaveHistory()
                stvsRootModel.autosaveSession()
            } catch (e: IOException) {
                AlertFactory.createAlert(
                    Alert.AlertType.ERROR,
                    "Autosave error",
                    "Error saving the current" + " configuration",
                    "The current configuration could not be saved.",
                    e.message,
                ).showAndWait()
            } catch (e: ExportException) {
                AlertFactory.createAlert(
                    Alert.AlertType.ERROR,
                    "Autosave error",
                    "Error saving the current" + " configuration",
                    "The current configuration could not be saved.",
                    e.message,
                ).showAndWait()
            }
        }
    }

    fun shouldBeMaximizedProperty(): BooleanProperty = rootModelProperty.get().globalConfig.windowMaximizedProperty
}