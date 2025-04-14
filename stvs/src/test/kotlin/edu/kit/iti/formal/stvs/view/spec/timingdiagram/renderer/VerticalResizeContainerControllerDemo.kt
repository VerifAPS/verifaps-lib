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