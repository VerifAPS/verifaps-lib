package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController;
import javafx.application.Application;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.Scene;
import javafx.scene.layout.VBox;
import org.junit.Test;

import java.io.File;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Created by csicar on 08.02.17.
 */
public class StvsRootControllerTest {

  @Test
  public void superSimpleTestcase() {
    JavaFxTest.runView(() -> simpleScene("session_super_simple_testcase.xml"));
  }

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(() -> simpleScene("session_valid_2.xml"));
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene(String sessionfile) {
    StvsRootModel rootModel = new StvsRootModel();
    try {
       rootModel = ImporterFacade.importSession(XmlSessionImporterTest.class
          .getResourceAsStream(sessionfile), ImporterFacade.ImportFormat.XML);
    } catch(Exception e) {
      e.printStackTrace();
    }

    GlobalConfig userConfig = null;
    try {
      userConfig = TestUtils.getUserConfig();
    } catch (UnknownHostException e) {
      e.printStackTrace();
    } catch (ImportException e) {
      e.printStackTrace();
    }
    if (userConfig != null) {
      rootModel.setGlobalConfig(userConfig);
    }

    StvsMainScene scene = new StvsMainScene(rootModel);

    return scene.getScene();
  }

}