package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.Demo;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import javafx.application.Application;
import javafx.scene.Scene;
import org.junit.Test;
import org.junit.experimental.categories.Category;

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