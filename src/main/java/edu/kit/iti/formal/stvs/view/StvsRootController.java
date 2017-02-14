package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.ViewUtils;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.verification.VerificationException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPaneController;
import edu.kit.iti.formal.stvs.view.spec.VerificationEvent;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.Alert;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * @author Carsten Csiky
 * @author Benjamin Alt
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
    this.editorPaneController = new EditorPaneController(
        stvsRootModel.getScenario().getCode(),
        stvsRootModel.getGlobalConfig()
    );

    this.types = new SimpleObjectProperty<>(typesFromCode(stvsRootModel.getScenario().getCode().getParsedCode()));
    this.ioVars = new SimpleObjectProperty<>(ioVarsFromCode(stvsRootModel.getScenario().getCode().getParsedCode()));
    this.specificationsPaneController = new SpecificationsPaneController(
        stvsRootModel.getHybridSpecifications(),
        stvsRootModel.getScenario().verificationState(),
        types,
        ioVars,
        stvsRootModel.getGlobalConfig()
    );

    this.stvsRootModel.getScenario().codeObjectProperty().addListener(this::onCodeChange);
    this.stvsRootModel.getScenario().getCode().parsedCodeProperty().addListener(this::parsedCodeChange);
    this.stvsRootModel.getScenario().verificationResultProperty().addListener(new
        VerificationResultListener());

    this.view = new StvsRootView(
        editorPaneController.getView(),
        specificationsPaneController.getView());

    view.addEventHandler(VerificationEvent.EVENT_TYPE,
        this::onVerificationEvent);
  }

  private void onVerificationEvent(VerificationEvent event) {
    switch(event.getType()) {
      case START:
        try {
          stvsRootModel.getScenario().verify(stvsRootModel.getGlobalConfig().getGetetaFilename(),
              stvsRootModel.getGlobalConfig().getNuxmvFilename(),
              event.getConstraintSpec());
        } catch (ExportException | IOException e) {
          ViewUtils.showDialog(Alert.AlertType.ERROR, "Export error", "An error occurred during " +
              "export of the specification:\n" + e.getMessage(), e.getStackTrace().toString());
        } catch (VerificationException e) {
          switch (e.getReason()) {
            case GETETA_NOT_FOUND:
              ViewUtils.showDialog(Alert.AlertType.ERROR, "GeTeTa executable not found",
                  "GeTeTa executable not found", "The GeTeTa executable could not be found.");
              break;
            case NUXMV_NOT_FOUND:
              ViewUtils.showDialog(Alert.AlertType.ERROR, "NuXmv executable not found",
                  "NuXmv executable not found", "The NuXmv executable could not be found.");
              break;
          }
        }
        break;
      case STOP:
        stvsRootModel.getScenario().cancel();
        ViewUtils.showDialog(Alert.AlertType.INFORMATION, "Verification cancelled",
            "Verification cancelled", "");
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

  private void onCodeChange(ObservableValue<? extends Code> observableValue, Code old, Code code) {
    editorPaneController = new EditorPaneController(code, stvsRootModel.getGlobalConfig());
    code.parsedCodeProperty().addListener(this::parsedCodeChange);
    view.setEditor(editorPaneController.getView());
  }

  private void parsedCodeChange(ObservableValue<? extends ParsedCode> o, ParsedCode old, ParsedCode parsedCode) {
    if (parsedCode != null) {
      types.set(typesFromCode(parsedCode));
      ioVars.set(ioVarsFromCode(parsedCode));
    }
  }

  private class VerificationResultListener implements
      javafx.beans.value.ChangeListener<edu.kit.iti.formal.stvs.model.verification.VerificationResult> {

    @Override
    public void changed(ObservableValue<? extends VerificationResult> observableValue,
                        VerificationResult oldResult, VerificationResult newResult) {
      onVerificationResultChanged();
    }
  }

  private void onVerificationResultChanged() {
    VerificationResult res = stvsRootModel.getScenario().getVerificationResult();
    // Inform the user about the verification result
    if (res == null) {
      ViewUtils.showDialog(Alert.AlertType.ERROR, "Verification error", "Verification " +
          "result is null", "");
    }
    String alertBody = "See the log at " + res.getLogFilePath();
    switch (res.getStatus()) {
      case COUNTEREXAMPLE:
        ViewUtils.showDialog(Alert.AlertType.INFORMATION, "Counterexample available",
            "Counterexample available", alertBody);
        break;
      case VERIFIED:
        ViewUtils.showDialog(Alert.AlertType.INFORMATION, "Verification successful",
            "Verification successful", alertBody);
        break;
      case ERROR:
        ViewUtils.showDialog(Alert.AlertType.ERROR, "Verification error",
            "Verification error", alertBody);
        break;
      case FATAL:
        ViewUtils.showDialog(Alert.AlertType.ERROR, "Verification error", "Fatal verification " +
            "error", alertBody);
        break;
      case UNKNOWN:
        ViewUtils.showDialog(Alert.AlertType.ERROR, "Unknown error", "Unknown verification " +
            "error", alertBody);
    }

    // TODO: Change the verification buttons to "play" again
  }
}
