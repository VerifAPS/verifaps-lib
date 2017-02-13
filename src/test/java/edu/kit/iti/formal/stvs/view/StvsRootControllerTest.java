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

  private static final Map<String, String> getetaFilenames;
  static
  {
    getetaFilenames = new HashMap<String, String>();
    getetaFilenames.put("bal", "/home/bal/Downloads/geteta-0.4.0-exe.jar");
  }

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    Scene scene = new Scene(new VBox(), 400, 350);
    StvsRootModel rootModel = new StvsRootModel();
    try {
       rootModel = ImporterFacade.importSession(XmlSessionImporterTest.class
          .getResourceAsStream("session_valid_2.xml"), ImporterFacade.ImportFormat.XML);
    }catch(Exception e) {
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

    StvsRootController rootController = new StvsRootController(rootModel);

    ((VBox) scene.getRoot()).getChildren().addAll(rootController.getView());

    return scene;
  }

}