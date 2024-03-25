package edu.kit.iti.formal.stvs.view

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.scene.Scene
import javafx.scene.control.Alert
import javafx.scene.layout.Priority
import javafx.scene.layout.VBox
import tornadofx.getValue
import tornadofx.setValue
import java.io.IOException

/**
 * Main Scene that holds all visible nodes of the program.
 *
 * @author Lukas Fritsch
 */
class StvsMainScene(rootModel: StvsRootModel = StvsRootModel.autoloadSession()) {

    private val rootModelProperty = SimpleObjectProperty(rootModel)
    var rootModel by rootModelProperty

    var rootController: StvsRootController = StvsRootController(rootModelProperty.get())

    val menuBarController: StvsMenuBarController = StvsMenuBarController(rootModelProperty)

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
            createVBox(), rootModel.globalConfig.windowWidth.toDouble(),
            rootModel.globalConfig.windowHeight.toDouble()
        )

        rootModel.globalConfig.windowWidthProperty.bind(scene.widthProperty())
        rootModel.globalConfig.windowHeightProperty.bind(scene.heightProperty())
    }

    private fun createVBox(): VBox {
        val vbox = VBox()
        vbox.children.addAll(menuBarController.view, rootController.view)
        VBox.setVgrow(rootController.view, Priority.ALWAYS)

        return vbox
    }

    private fun rootModelChanged(rootModel: StvsRootModel) {
        this.rootController = StvsRootController(rootModel)
        scene.root = createVBox()
    }

    /**
     * Code that should be executed before the scene is destroyed on exit.
     */
    fun onClose() {
        val stvsRootModel: StvsRootModel = rootModelProperty.get()
        if (stvsRootModel != null) {
            try {
                stvsRootModel.globalConfig.autosaveConfig()
                stvsRootModel.history.autosaveHistory()
                stvsRootModel.autosaveSession()
            } catch (e: IOException) {
                AlertFactory.createAlert(
                    Alert.AlertType.ERROR, "Autosave error",
                    "Error saving the current" + " configuration",
                    "The current configuration could not be saved.", e.message
                ).showAndWait()
            } catch (e: ExportException) {
                AlertFactory.createAlert(
                    Alert.AlertType.ERROR, "Autosave error",
                    "Error saving the current" + " configuration",
                    "The current configuration could not be saved.", e.message
                ).showAndWait()
            }
        }
    }

    fun shouldBeMaximizedProperty(): BooleanProperty {
        return rootModelProperty.get().globalConfig.windowMaximizedProperty
    }
}
