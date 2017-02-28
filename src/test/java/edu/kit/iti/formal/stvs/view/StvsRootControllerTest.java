package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporterTest;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.view.common.FileChooserFactory;
import edu.kit.iti.formal.stvs.view.editor.EditorPane;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramView;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.scene.Scene;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mockito;
import org.powermock.api.mockito.PowerMockito;
import org.powermock.core.classloader.annotations.PowerMockIgnore;
import org.powermock.core.classloader.annotations.PrepareForTest;
import org.powermock.modules.junit4.PowerMockRunner;
import org.testfx.framework.junit.ApplicationTest;

import java.io.File;
import java.net.URL;
import java.util.Arrays;
import java.util.concurrent.TimeUnit;

import static org.mockito.ArgumentMatchers.any;
import static org.testfx.api.FxAssert.verifyThat;

/**
 * Created by csicar on 08.02.17.
 */
@RunWith(PowerMockRunner.class)
@PrepareForTest({StvsMenuBarController.class, StvsRootController.class, FileChooser.class,
    FileChooserFactory.class})
@PowerMockIgnore({ "javax.xml.*", "org.xml.sax.*", "com.sun.xml.*", "com.sun.org.*",
    "org.w3c.dom.*"})
public class StvsRootControllerTest extends ApplicationTest {

  private Scene simpleScene(String sessionfile) {
    StvsRootModel rootModel = new StvsRootModel();
    try {
      rootModel = ImporterFacade.importSession(XmlSessionImporterTest.class
              .getResourceAsStream(sessionfile), ImporterFacade.ImportFormat.XML, new GlobalConfig(),
          new History());
    } catch (Exception e) {
      e.printStackTrace();
    }

    StvsMainScene scene = new StvsMainScene(rootModel);

    return scene.getScene();
  }


  @Test
  public void testSzenarioBob() throws Exception {
    TestUtils.mockFiles(
        GeTeTaImporterTest.class.getResource("code_successful_enums.st"),
        XmlSessionImporterTest.class.getResource("spec_constraint_valid_1.xml"));
    clickOn("File")
        .clickOn("Open");
    verifyThat("#EditorPane", (EditorPane pane) -> {
      return pane.getCodeArea().getText().contains("PROGRAM ppp\n" +
          "  VAR i : INT; END_VAR\n" +
          "  VAR_OUTPUT o : abc; END_VAR\n" +
          "\n" +
          "  o := SEL(i = 0, abc#a,\n" +
          "  SEL(i = 1, abc#b, abc#c));\n" +
          "  i := i + 1;\n" +
          "  i := SEL(i>2, 0, i);\n" +
          "END_PROGRAM");
    });
    clickOn("File").clickOn("Open ...").clickOn("Open Specification");
    sleep(10000);
    verifyThat("#TimingDiagramView", (TimingDiagramView<?> v) -> {
      return v.getChildrenUnmodifiable().size() > 1;
    });
    sleep(5, TimeUnit.SECONDS);
    System.exit(0);
  }


  @Override
  public void start(Stage stage) throws Exception {
    stage.setScene(simpleScene("session_valid_2.xml"));
    stage.show();

  }

  @Test
  @Ignore
  public void superSimpleTestcase() {
    JavaFxTest.runView(() -> simpleScene("session_super_simple_testcase.xml"));
  }

  @Test
  @Ignore
  public void testDemo() {
    JavaFxTest.runView(() -> simpleScene("demo_session.xml"));
  }

  @Test
  @Ignore
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(() -> simpleScene("session_valid_2.xml"));
    Application.launch(JavaFxTest.class);
  }
}