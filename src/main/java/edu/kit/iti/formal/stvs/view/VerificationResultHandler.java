package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.*;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;

import java.io.IOException;
import java.util.Optional;

import javafx.scene.control.Alert;
import org.apache.commons.io.FileUtils;

/**
 * Handles a verification result on the view side: Shows the appropriate dialogs depending on the
 * result type, etc.
 */
public class VerificationResultHandler implements VerificationResultVisitor {

  private final StvsRootController controller;
  private String logFileContents;
  private String alertBody;

  /**
   * Creates an instance of this visitor.
   * @param controller root controller from which the rootModel is taken
   */
  public VerificationResultHandler(StvsRootController controller) {
    this.controller = controller;
    alertBody = "Verification done.";
    logFileContents = "";
  }

  /**
   * Visits a {@link Counterexample}.
   * This displays the counterexample in a new tab.
   * @param result Counterexample to visit.
   */
  public void visitCounterexample(Counterexample result) {
    makeAlertBody(result);
    AlertFactory.createAlert(Alert.AlertType.INFORMATION, "Counterexample Available",
        "A counterexample is available.", alertBody, logFileContents).showAndWait();
    StvsRootModel rootModel = controller.getRootModel();
    // Show read-only copy of spec with counterexample in a new tab
    Optional<ConstraintSpecification> verifiedSpec = rootModel.getScenario()
        .getVerificationEngine().getCurrentSpec();
    assert verifiedSpec.isPresent();
    HybridSpecification readOnlySpec = new HybridSpecification(
        new ConstraintSpecification(verifiedSpec.get()), false);
    readOnlySpec.setCounterExample(result.getCounterexample());
    rootModel.getHybridSpecifications().add(readOnlySpec);
  }

  /**
   * Visits a {@link VerificationError}.
   * This displays an appropriate error dialog.
   * @param result error to visit
   */
  public void visitVerificationError(VerificationError result) {
    String expandableContent = "";
    if (result.getLogFile().isPresent()) {
      try {
        expandableContent = FileUtils.readFileToString(result.getLogFile().get(), "utf-8");
      } catch (IOException ex) {
        // Do nothing, don't want to distract from the actual error
      }
    }
    AlertFactory
        .createAlert(Alert.AlertType.ERROR, "Verification Error",
            "An error occurred during verification.", result.getMessage(), expandableContent)
        .showAndWait();
  }

  /**
   * Visits a {@link VerificationSuccess}.
   * This displays an appropriate success dialog.
   * @param result success to visit
   */
  public void visitVerificationSuccess(VerificationSuccess result) {
    makeAlertBody(result);
    AlertFactory.createAlert(Alert.AlertType.INFORMATION, "Verification Successful",
        "The verification completed successfully.", alertBody, logFileContents).showAndWait();
  }

  private void makeAlertBody(VerificationResult result) {
    if (result.getLogFile().isPresent()) {
      alertBody = " See the log at " + result.getLogFile().get().getAbsolutePath() + ".";
      try {
        logFileContents = FileUtils.readFileToString(result.getLogFile().get(), "utf-8");
      } catch (IOException ex) {
        // Do nothing, don't want to distract from the result
      }
    }
  }
}
