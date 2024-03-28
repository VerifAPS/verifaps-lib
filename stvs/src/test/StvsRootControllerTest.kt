package edu.kit.iti.formal.stvs.view

import edu.kit.iti.formal.stvs.*
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporterTest
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.view.common.FileChooserFactory
import edu.kit.iti.formal.stvs.view.editor.EditorPane
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController
import javafx.scene.Scene
import javafx.stage.FileChooser
import javafx.stage.Stage
import javafx.stage.StageStyle
import org.junit.Ignore
import org.junit.jupiter.api.Test
import org.junit.runner.RunWith
import org.powermock.core.classloader.annotations.PowerMockIgnore
import org.powermock.core.classloader.annotations.PrepareForTest
import org.powermock.modules.junit4.PowerMockRunner
import org.testfx.api.FxAssert
import org.testfx.api.FxToolkit
import org.testfx.framework.junit.ApplicationTest

/**
 * Created by csicar on 08.02.17.
 */
@Ignore
@RunWith(PowerMockRunner::class)
@PrepareForTest(
    StvsMenuBarController::class, StvsRootController::class, FileChooser::class, FileChooserFactory::class
)
@PowerMockIgnore(
    "javax.xml.*", "org.xml.sax.*", "com.sun.xml.*", "com.sun.org.*", "org.w3c.dom.*"
)
class StvsRootControllerTest : ApplicationTest() {
    private fun simpleScene(sessionfile: String): Scene {
        var rootModel: StvsRootModel? = StvsRootModel()
        try {
            rootModel = ImporterFacade.importSession(
                XmlSessionImporterTest::class.java.getResourceAsStream(sessionfile)!!,
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
    @Throws(Exception::class)
    fun testSzenarioBob() {
        TestUtils.mockFiles(
            GeTeTaImporterTest::class.java.getResource("code_successful_enums.st")!!,
            XmlSessionImporterTest::class.java.getResource("spec_constraint_valid_1.xml")!!
        )
        clickOn("File")
            .clickOn("Open")
        FxAssert.verifyThat("#EditorPane") { pane: EditorPane ->
            pane.codeArea.text.contains(
                """PROGRAM ppp
  VAR i : INT; END_VAR
  VAR_OUTPUT o : abc; END_VAR

  o := SEL(i = 0, abc#a,
  SEL(i = 1, abc#b, abc#c));
  i := i + 1;
  i := SEL(i>2, 0, i);
END_PROGRAM"""
            )
        }
        clickOn("File").clickOn("Open ...").clickOn("Open Specification")
        //TODO: fix deconstruction
        //assertEquals(0, lookup("#TimingDiagramView").queryAll().size());
        clickOn("#EditorPane").rightClickOn().clickOn("Select All")
        write(
            """VAR_INPUT
        Start_Stop  : BOOL;
        ON_OFF      : BOOL;
    END_VAR"""
        )
    }


    @Throws(Exception::class)
    override fun start(stage: Stage) {
        stage.scene = simpleScene("session_valid_2.xml")
        stage.initStyle(StageStyle.DECORATED)
        stage.show()
    }

    @Throws(Exception::class)
    override fun stop() {
        FxToolkit.hideStage()
    }
}