package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecImporter;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.CodeTest;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.net.URISyntaxException;
import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.*;

/**
 * Created by leonk on 02.02.2017.
 */
public class TimingDiagramCollectionControllerTest {

  @Test
  public void javaFxTest(){
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene(){
    try {
      XmlConcreteSpecImporter importer = new XmlConcreteSpecImporter();
      FileInputStream inputStream = new FileInputStream(new File
          (XmlConcreteSpecImporter.class.getResource("spec_concrete_valid_1.xml").toURI()));
      ConcreteSpecification importedSpec = importer.doImport(inputStream);

      Selection selection = new Selection();
      TimingDiagramCollectionController controller = new TimingDiagramCollectionController(importedSpec, selection);

      TextArea console = new TextArea();

      selection.columnProperty().addListener(change -> {
        console.appendText("Selection column set to: " + selection.getColumn() + "\n");
      });
      selection.rowProperty().addListener(change -> {
        console.appendText("Selection row set to: " + selection.getRow() + "\n");
      });

      VBox root = new VBox();
      root.getChildren().addAll(controller.getView(), console);
      Scene scene = new Scene(root, 800, 600);
      //scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
      return scene;
    }
    catch(Exception e){
      e.printStackTrace();
      return null;
    }
  }

  /*private static HybridSpecification createExampleSpecification(){
    ConcreteSpecification spec = new ConcreteSpecification(false);
    spec.
  }*/
}