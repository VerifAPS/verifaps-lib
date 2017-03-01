package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.TestUtils;
import javafx.scene.Scene;
import javafx.scene.layout.HBox;
import javafx.stage.Stage;
import org.junit.Before;
import org.junit.Test;
import org.testfx.framework.junit.ApplicationTest;
import org.testfx.service.query.NodeQuery;

import javax.swing.text.TableView;

import static org.junit.Assert.*;

/**
 * Created by csicar on 01.03.17.
 */
public class VariableCollectionTest extends ApplicationTest {
  private VariableCollection collection;

  @Test
  public void doesNotAllowDuplicates() {
    TestUtils.gimmeTime();
  }

  @Override
  public void start(Stage stage) throws Exception {
    collection = new VariableCollection();
    stage.setScene(new Scene(collection));
    stage.show();
  }
}