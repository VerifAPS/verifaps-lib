package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.scene.Scene;
import javafx.scene.control.TableColumn;
import org.junit.Test;
import org.reactfx.value.Var;

import static org.junit.Assert.*;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SpecificationTableTest {

  @Test
  public void testTable() {
    JavaFxTest.runView(this::simpleTableScene);
  }

  private Scene simpleTableScene() {
    SpecificationTableController table = new SpecificationTableController();

    table.addColumn(VariableCategory.INPUT, "A");
    table.addColumn(VariableCategory.INPUT, "B");

    table.addRow(new HybridRowModel("-").add("A", "-").add("B", "-"));

    table.addColumn(VariableCategory.OUTPUT, "C");

    table.addRow(new HybridRowModel("1").add("A", "2").add("B", "3").add("C", "4"));

    return new Scene(table.getView(), 800, 600);
  }

}