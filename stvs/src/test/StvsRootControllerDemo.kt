package edu.kit.iti.formal.stvs.view

import edu.kit.iti.formal.stvs.Demo
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import javafx.application.Application
import javafx.scene.Scene
import org.junit.jupiter.api.Test
import org.junit.experimental.categories.Category

/**
 * Created by csicar on 08.02.17.
 */
@Category(Demo::class)
class StvsRootControllerDemo {
    private fun simpleScene(sessionFile: String): Scene {
        var rootModel: StvsRootModel? = StvsRootModel()
        try {
            rootModel = ImporterFacade.importSession(
                XmlSessionImporterTest::class.java.getResourceAsStream(sessionFile)!!,
                GlobalConfig(),
                History()
            )
        } catch (e: Exception) {
            e.printStackTrace()
        }

        val scene = StvsMainScene(rootModel!!)

        return scene.scene
    }


    @Test
    fun superSimpleTestcase() {
        JavaFxTest.runView { simpleScene("session_super_simple_testcase.xml") }
    }

    @Test
    fun testDemo() {
        JavaFxTest.runView { simpleScene("demo_session.xml") }
    }

    @Test
    fun javaFxTest() {
        JavaFxTest.setToBeViewed { simpleScene("session_valid_2.xml") }
        Application.launch(JavaFxTest::class.java)
    }
}