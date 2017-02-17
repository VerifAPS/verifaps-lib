package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.verification.VerificationException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.view.common.ErrorMessageDialog;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPaneController;
import edu.kit.iti.formal.stvs.view.spec.VerificationEvent;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.Alert;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
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
        stvsRootModel.getGlobalConfig(),
        stvsRootModel.getScenario()
    );

    this.stvsRootModel.getScenario().codeObjectProperty().addListener(this::onCodeChange);
    this.stvsRootModel.getScenario().getCode().parsedCodeProperty().addListener(this::parsedCodeChange);
    this.stvsRootModel.getScenario().verificationResultProperty().addListener(this::onVerificationResultChange);

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
          stvsRootModel.getScenario().verify(stvsRootModel.getGlobalConfig(), event
              .getConstraintSpec());
        } catch (ExportException | IOException e) {
          ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "Export error", "An error occurred during " +
              "export of the specification:\n" + e.getMessage(), e.getStackTrace().toString());
        } catch (VerificationException e) {
          switch (e.getReason()) {
            case GETETA_NOT_FOUND:
              ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "GeTeTa executable not found",
                  "GeTeTa executable not found", "The GeTeTa executable could not be found.");
              break;
            case NUXMV_NOT_FOUND:
              ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "NuXmv executable not found",
                  "NuXmv executable not found", "The NuXmv executable could not be found.");
              break;
          }
        }
        break;
      case STOP:
        stvsRootModel.getScenario().cancel();
        ErrorMessageDialog.createMessageDialog(Alert.AlertType.INFORMATION, "Verification cancelled",
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

  private void onVerificationResultChange(ObservableValue<? extends VerificationResult> o,
                                           VerificationResult old, VerificationResult res) {
    // Inform the user about the verification result
    if (res == null) {
      ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "Verification Error", "Verification " +
          "result is null", "");
    }
    String alertBody = "See the log at " + res.getLogFilePath() + ".";
    String logFileContents = "";
    try {
      logFileContents = new String(Files.readAllBytes(Paths.get(res.getLogFilePath())), "utf-8");
    } catch (IOException e) {
      ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "Logging Error", "Could not write log file",
          "There was an error writing the log file: " + res.getLogFilePath(), e.getStackTrace()
              .toString());
      return;
    }
    switch (res.getStatus()) {
      case COUNTEREXAMPLE:
        ErrorMessageDialog.createMessageDialog(Alert.AlertType.INFORMATION, "Counterexample Available",
            "A counterexample is available", alertBody, logFileContents);
        // Show read-only copy of spec with counterexample in a new tab
        assert stvsRootModel.getScenario().getActiveSpec() != null;
        HybridSpecification readOnlySpec = new HybridSpecification(stvsRootModel.getScenario()
            .getActiveSpec(), false);
        readOnlySpec.setCounterExample(res.getCounterExample());
        specificationsPaneController.addTab(readOnlySpec);
        break;
      case VERIFIED:
        ErrorMessageDialog.createMessageDialog(Alert.AlertType.INFORMATION, "Verification Successful",
            "The verification completed successfully.", alertBody, logFileContents);
        break;
      case TIMEOUT:
        ErrorMessageDialog.createMessageDialog(Alert.AlertType.WARNING, "Verification Timeout",
            "The verification timed out.", "Current timeout: " + stvsRootModel.getGlobalConfig()
                .getVerificationTimeout() + " seconds");
        break;
      case ERROR:
        ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "Verification Error",
            "An error occurred during verification.", alertBody, logFileContents);
        break;
      case FATAL:
        ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "Verification Error", "A fatal " +
            "error occurred during verification.", alertBody, logFileContents);
        break;
      case UNKNOWN:
        ErrorMessageDialog.createMessageDialog(Alert.AlertType.ERROR, "Unknown Error", "An unknown error " +
            "occurred during verification.", alertBody, logFileContents);
    }
  }
}
