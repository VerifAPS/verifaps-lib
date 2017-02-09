package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporter;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.io.File;
import java.io.IOException;

/**
 * @author Benjamin Alt
 * Handles communication with the GeTeTa verification engine
 */
public class GeTeTaVerificationEngine implements VerificationEngine {
  private GeTeTaImporter importer;
  private Process getetaProcess;
  private NullableProperty<VerificationResult> verificationResult;

  private final String GETETA_VERSION = "0.2.2-beta";
  private final String GETETA_COMMAND_BASE = "java -jar geteta-" + GETETA_VERSION + ".jar";

  public GeTeTaVerificationEngine() {
    importer = new GeTeTaImporter();
    verificationResult = new NullableProperty<>();
    getetaProcess = null;
  }

  @Override
  public void startVerification(VerificationScenario scenario, ConstraintSpecification spec) throws
      IOException, ExportException {
    // Write ConstraintSpecification and Code to temporary files
    File tempSpecFile = File.createTempFile("verification-spec", ".xml");
    ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.GETETA, tempSpecFile);
    ExporterFacade.exportCode(scenario.getCode());
    // Start verification engine in new child process
    String getetaCommand = GETETA_COMMAND_BASE + " -c " + scenario.getCode().getFilename() + " -t" +
        " " + tempSpecFile.getAbsolutePath() + " -x";
    if (getetaProcess != null) {
      cancelVerification();
    }
    getetaProcess = Runtime.getRuntime().exec(getetaCommand);
    // Find out when process finishes to set verification result property
    ProcessExitDetector exitDetector = new ProcessExitDetector(getetaProcess);
    exitDetector.processFinishedProperty().addListener(new VerificationDoneListener());
  }

  @Override
  public void cancelVerification() {
    if (getetaProcess != null) {
      getetaProcess.destroy();
      getetaProcess = null;
    }
  }

  @Override
  public VerificationResult getVerificationResult() {
    return verificationResult.get();
  }

  public NullableProperty<VerificationResult> verificationResultProperty() {
    return verificationResult;
  }

  private class VerificationDoneListener implements ChangeListener<Boolean> {
    @Override
    public void changed(ObservableValue<? extends Boolean> observableValue, Boolean oldValue,
                        Boolean newValue) {
      onVerificationDone();
    }
  }

  private void onVerificationDone() {
    System.out.println("Verification done!");
  }
}
