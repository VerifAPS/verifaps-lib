package edu.kit.iti.formal.stvs.view.menu

import org.junit.jupiter.api.Tag
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.application.Application
import javafx.beans.property.SimpleObjectProperty
import javafx.scene.Scene
import javafx.scene.layout.VBox
import org.junit.jupiter.api.Test
import java.util.function.Supplier

/**
 * Created by csicar on 30.01.17.
 */
@Tag("demo")
class StvsMenuBarDemo {
    @Test
    fun javaFxTest() {
        JavaFxTest.Companion.setToBeViewed(Supplier<Scene?> { this.simpleScene() })
        Application.launch(JavaFxTest::class.java)
    }

    private fun simpleScene(): Scene {
        val scene = Scene(VBox(), 400.0, 350.0)

        val rootModel = StvsRootModel()

        val menuBarController = StvsMenuBarController(SimpleObjectProperty(rootModel))
        (scene.root as VBox).children.addAll(menuBarController.view)

        return scene
    }
}
