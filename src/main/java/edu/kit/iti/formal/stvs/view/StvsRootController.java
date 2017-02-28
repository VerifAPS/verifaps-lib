package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationError;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPaneController;
import edu.kit.iti.formal.stvs.view.spec.VerificationEvent;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.Alert;
import org.apache.commons.io.FileUtils;

/**
 * @author Carsten Csiky
 */
public class StvsRootController implements Controller {

  private final StvsRootView view;
  private final StvsRootModel stvsRootModel;
  private final ObjectProperty<List<Type>> types;
  private final ObjectProperty<List<CodeIoVariable>> ioVars;
  private final SpecificationsPaneController specificationsPaneController;
  private EditorPaneController editorPaneController;

  public StvsRootController(StvsRootModel rootModel) {
    this.stvsRootModel = rootModel;
    this.editorPaneController = new EditorPaneController(stvsRootModel.getScenario().getCode(),
        stvsRootModel.getGlobalConfig());

    this.types = new SimpleObjectProperty<>(
        typesFromCode(stvsRootModel.getScenario().getCode().getParsedCode()));
    this.ioVars = new SimpleObjectProperty<>(
        ioVarsFromCode(stvsRootModel.getScenario().getCode().getParsedCode()));
    this.specificationsPaneController = new SpecificationsPaneController(
        stvsRootModel.getHybridSpecifications(), stvsRootModel.getScenario().verificationState(),
        types, ioVars, stvsRootModel.getGlobalConfig(), stvsRootModel.getScenario());

    this.stvsRootModel.getScenario().codeObjectProperty().addListener(this::onCodeChange);
    this.stvsRootModel.getScenario().getCode().parsedCodeProperty()
        .addListener(this::onParsedCodeChange);
    this.stvsRootModel.getScenario().verificationResultProperty()
        .addListener(this::onVerificationResultChange);

    this.view =
        new StvsRootView(editorPaneController.getView(), specificationsPaneController.getView());

    view.addEventHandler(VerificationEvent.EVENT_TYPE, this::onVerificationEvent);
  }

  /**
   * Handles verification events (triggers start or cancel of verification depending on the event
   * type).
   *
   * @param event The verification event
   */
  private void onVerificationEvent(VerificationEvent event) {
    switch (event.getType()) {
      case START:
        try {
          stvsRootModel.getScenario().verify(stvsRootModel.getGlobalConfig(),
              event.getConstraintSpec());
        } catch (ExportException | IOException | VerificationError e) {
          AlertFactory
              .createAlert(e, "Verification Error", "The verification " + "could not be started.")
              .showAndWait();
          stvsRootModel.getScenario().cancel();
        }
        break;
      case STOP:
        stvsRootModel.getScenario().cancel();
        AlertFactory.createAlert(Alert.AlertType.INFORMATION, "Verification cancelled",
            "Verification cancelled.", "").showAndWait();
    }
  }

  private List<CodeIoVariable> ioVarsFromCode(ParsedCode parsedCode) {
    if (parsedCode == null) {
      return Collections.emptyList();
    }
    return parsedCode.getDefinedVariables();
  }

  private List<Type> typesFromCode(ParsedCode parsedCode) {
    if (parsedCode == null) {
      return Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    }
    return parsedCode.getDefinedTypes();
  }

  public StvsRootView getView() {
    return view;
  }

  /**
   * Change handler for the code. Updates the editor on code changes.
   *
   * @param observableValue The observable value
   * @param old The code before the change
   * @param code The code after the change
   */
  private void onCodeChange(ObservableValue<? extends Code> observableValue, Code old, Code code) {
    editorPaneController = new EditorPaneController(code, stvsRootModel.getGlobalConfig());
    code.parsedCodeProperty().addListener(this::onParsedCodeChange);
    view.setEditor(editorPaneController.getView());
  }

  /**
   * Change handler for the parsed code. Updates types and IO variables depending on those declared
   * in the new parsed code.
   *
   * @param o The observable value
   * @param old The parsed code before the change
   * @param parsedCode The parsed code after the change
   */
  private void onParsedCodeChange(ObservableValue<? extends ParsedCode> o, ParsedCode old,
      ParsedCode parsedCode) {
    if (parsedCode != null) {
      types.set(typesFromCode(parsedCode));
      ioVars.set(ioVarsFromCode(parsedCode));
    }
  }

  /**
   * Change handler for the verification result. Informs the user about the result of a verification
   * and opens counterexamples in a new tab, if a counterexample is available.
   *
   * @param o The observable value
   * @param old The verification result before the change
   * @param res The verification result after the change
   */
  private void onVerificationResultChange(ObservableValue<? extends VerificationResult> o,
      VerificationResult old, VerificationResult res) {
    if (res == null) {
      AlertFactory.createAlert(Alert.AlertType.ERROR, "Verification Error",
          "Verification result is null", "").showAndWait();
    }
    try {
      String logFileContents = "";
      String alertBody = "Verification done.";
      if (res.getLogFile().isPresent()) {
        alertBody = " See the log at " + res.getLogFile().get().getAbsolutePath() + ".";
        logFileContents = FileUtils.readFileToString(res.getLogFile().get(), "utf-8");
      }
      switch (res.getStatus()) {

        case COUNTEREXAMPLE:
          AlertFactory.createAlert(Alert.AlertType.INFORMATION, "Counterexample Available",
              "A counterexample is available.", alertBody, logFileContents).showAndWait();
          // Show read-only copy of spec with counterexample in a new tab
          assert stvsRootModel.getScenario().getActiveSpec() != null;
          assert res.getCounterExample().isPresent();
          HybridSpecification readOnlySpec = new HybridSpecification(
              new ConstraintSpecification(stvsRootModel.getScenario().getActiveSpec()), false);
          readOnlySpec.setCounterExample(res.getCounterExample().get());
          stvsRootModel.getHybridSpecifications().add(readOnlySpec);
          break;

        case VERIFIED:
          AlertFactory
              .createAlert(Alert.AlertType.INFORMATION, "Verification Successful",
                  "The verification completed successfully.", alertBody, logFileContents)
              .showAndWait();
          break;

        default:
          AlertFactory.createAlert(res.getVerificationError().get()).showAndWait();
      }
    } catch (IOException e) {
      AlertFactory.createAlert(e).showAndWait();
    }
  }
}
