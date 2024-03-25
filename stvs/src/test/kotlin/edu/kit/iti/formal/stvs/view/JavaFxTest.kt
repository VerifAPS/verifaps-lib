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
