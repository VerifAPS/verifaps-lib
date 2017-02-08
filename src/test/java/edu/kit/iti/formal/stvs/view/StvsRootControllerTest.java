package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController;
import javafx.application.Application;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.Scene;
import javafx.scene.layout.VBox;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.*;

/**
 * Created by csicar on 08.02.17.
 */
public class StvsRootControllerTest {
  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    Scene scene = new Scene(new VBox(), 400, 350);
    XmlSessionImporterTest importer = new XmlSessionImporterTest();
    StvsRootModel rootModel = new StvsRootModel();
    try {
       rootModel = ImporterFacade.importSession(importer.getClass()
          .getResourceAsStream("session_valid_1.xml"), ImporterFacade.ImportFormat.XML);

    }catch(Exception e) {
      e.printStackTrace();
    }

    StvsRootController rootController = new StvsRootController(rootModel);

    ((VBox) scene.getRoot()).getChildren().addAll(rootController.getView());

    return scene;
  }

}