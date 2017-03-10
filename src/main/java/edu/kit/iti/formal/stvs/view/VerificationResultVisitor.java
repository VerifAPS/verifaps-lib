package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.Counterexample;
import edu.kit.iti.formal.stvs.model.verification.VerificationError;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;
import javafx.scene.control.Alert;
import org.apache.commons.io.FileUtils;

import java.io.IOException;

/**
 * Handles a verification result on the view side: Shows the appropriate dialogs depending on the
 * result type, etc.
 */
public class VerificationResultVisitor {

  private final StvsRootController controller;
  private String logFileContents;
  private String alertBody;

  public VerificationResultVisitor(StvsRootController controller) {
    this.controller = controller;
    alertBody = "Verification done.";
    logFileContents = "";
  }

  public void visitCounterexample(Counterexample result) {
    AlertFactory.createAlert(Alert.AlertType.INFORMATION, "Counterexample Available",
        "A counterexample is available.", alertBody, logFileContents).showAndWait();
    StvsRootModel rootModel = controller.getRootModel();
    // Show read-only copy of spec with counterexample in a new tab
    assert rootModel.getScenario().getActiveSpec() != null;
    HybridSpecification readOnlySpec = new HybridSpecification(
        new ConstraintSpecification(rootModel.getScenario().getActiveSpec()), false);
    readOnlySpec.setCounterExample(result.getCounterexample());
    rootModel.getHybridSpecifications().add(readOnlySpec);
  }

  public void visitVerificationError(VerificationError result) {
    String expandableContent = "";
    if (result.getLogFile().isPresent()) {
      try {
        expandableContent = FileUtils.readFileToString(result.getLogFile().get(), "utf-8");
      } catch (IOException ex) {
        // Do nothing, don't want to distract from the actual error
      }
    }
    AlertFactory.createAlert(Alert.AlertType.ERROR, "Verification Error",
        "An error occurred during verification.", result.getMessage(),
        expandableContent).showAndWait();
  }

  public void visitVerificationSuccess(VerificationSuccess result) {
    if (result.getLogFile().isPresent()) {
      alertBody = " See the log at " + result.getLogFile().get().getAbsolutePath() + ".";
      try {
        logFileContents = FileUtils.readFileToString(result.getLogFile().get(), "utf-8");
      } catch (IOException ex) {
        // Do nothing, don't want to distract from the result
      }
    }
    AlertFactory.createAlert(Alert.AlertType.INFORMATION, "Verification Successful",
        "The verification completed successfully.", alertBody, logFileContents).showAndWait();
  }
}
