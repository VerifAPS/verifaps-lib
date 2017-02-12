package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import org.apache.commons.io.IOUtils;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SpecificationTableTest {

  @Test
  public void testTable() {
    JavaFxTest.runSplitView(this::simpleTableScene);
  }

  private List<Node> simpleTableScene() {
    List<Type> types = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    List<CodeIoVariable> codevars = Arrays.asList(
        new CodeIoVariable(VariableCategory.INPUT, "BOOL", "A"),
        new CodeIoVariable(VariableCategory.INPUT, "INT", "B"),
        new CodeIoVariable(VariableCategory.OUTPUT, "INT", "C")
    );
    ObjectProperty<List<Type>> typeContext = new SimpleObjectProperty<>(types);
    ObjectProperty<List<CodeIoVariable>> codeIoVariables = new SimpleObjectProperty<>(codevars);

    FreeVariableList freeVariableList = new FreeVariableList(new ArrayList<>());

    FreeVariableListValidator freevarValidator = new FreeVariableListValidator(typeContext, freeVariableList);
    SpecificationTableController table = new SpecificationTableController(
        typeContext,
        codeIoVariables,
        freevarValidator.validFreeVariablesProperty(),
        new HybridSpecification(freeVariableList, true));
    Pane extractedTablePane = createExtractedTableTextArea(
        table.getHybridSpecification(),
        table.getSpecProblemRecognizer());

    return Arrays.asList(table.getView(), extractedTablePane);
  }

  private Pane createExtractedTableTextArea(ConstraintSpecification spec, ConstraintSpecificationValidator recognizer) {
    final TextArea textArea = new TextArea();
    textArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    updateText(textArea, spec);

    final Button updateButton = new Button("Refresh");
    updateButton.setOnAction(event -> updateText(textArea, spec));

    final TextArea problemsArea = new TextArea();
    problemsArea.getStyleClass().addAll("model-text-area");
    textArea.setEditable(false);

    updateProblemsText(problemsArea, recognizer);

    recognizer.problemsProperty().addListener((Observable o) -> updateProblemsText(problemsArea, recognizer));

    SplitPane splitPane = new SplitPane(textArea, problemsArea);
    splitPane.setOrientation(Orientation.VERTICAL);
    VBox.setVgrow(splitPane, Priority.ALWAYS);
    return new VBox(updateButton, splitPane);
  }

  private void updateProblemsText(TextArea problemsArea, ConstraintSpecificationValidator recognizer) {
    String error = String.join("\n", recognizer.problemsProperty().get().stream().map(
        specProblem -> specProblem.getClass().getSimpleName() + ": " + specProblem.getErrorMessage()
    ).collect(Collectors.toList()));
    problemsArea.setText(error);
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