package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;
import javafx.beans.InvalidationListener;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import org.apache.commons.io.IOUtils;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Arrays;
import java.util.List;
import java.util.Observable;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SpecificationTableTest {

  @Test
  public void testTable() {
    JavaFxTest.runSplitView(this::simpleTableScene);
  }

  private List<Node> simpleTableScene() {
    ObservableSet<Type> types = FXCollections.observableSet(TypeInt.INT, TypeBool.BOOL);
    ObservableSet<CodeIoVariable> codeIoVariables = FXCollections.observableSet();
    SpecificationTableController table = new SpecificationTableController(types, codeIoVariables, new FreeVariableSet());

    table.addColumn(VariableCategory.INPUT, "A");
    table.addColumn(VariableCategory.INPUT, "B");
    table.addColumn(VariableCategory.OUTPUT, "C");

    table.addEmptyRow(0);

    return Arrays.asList(table.getView(), createExtractedTableTextArea(table.getData()));
  }

  private Pane createExtractedTableTextArea(ConstraintSpecification spec) {
    final TextArea textArea = new TextArea();
    textArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    updateText(textArea, spec);
    // this is a hack, kinda
    spec.getDurations().addListener((ListChangeListener.Change<? extends ConstraintDuration> c) -> updateText(textArea, spec));

    return new StackPane(textArea);
  }

  private void updateText(TextArea textArea, ConstraintSpecification spec) {
    try {
      ByteArrayOutputStream stream = ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.XML);
      String output = IOUtils.toString(stream.toByteArray(), "UTF-8");
      textArea.setText(output);
    } catch (Exception e) {
      StringWriter writeString = new StringWriter();
      e.printStackTrace(new PrintWriter(writeString));
      e.printStackTrace();
      textArea.setText(writeString.toString());
    }
  }

}