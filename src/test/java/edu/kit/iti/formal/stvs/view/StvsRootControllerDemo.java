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
import javafx.scene.Scene;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.experimental.categories.Categories;
import org.junit.experimental.categories.Category;
import org.junit.runner.RunWith;
import org.powermock.core.classloader.annotations.PowerMockIgnore;
import org.powermock.core.classloader.annotations.PrepareForTest;
import org.powermock.modules.junit4.PowerMockRunner;
import org.testfx.framework.junit.ApplicationTest;

import static org.testfx.api.FxAssert.verifyThat;

/**
 * Created by csicar on 08.02.17.
 */
@Category(Demo.class)
public class StvsRootControllerDemo {

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
  public void superSimpleTestcase() {
    JavaFxTest.runView(() -> simpleScene("session_super_simple_testcase.xml"));
  }

  @Test
  public void testDemo() {
    JavaFxTest.runView(() -> simpleScene("demo_session.xml"));
  }

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(() -> simpleScene("session_valid_2.xml"));
    Application.launch(JavaFxTest.class);
  }
}