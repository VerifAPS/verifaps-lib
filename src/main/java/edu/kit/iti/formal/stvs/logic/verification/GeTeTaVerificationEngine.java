package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporter;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import org.apache.commons.io.IOUtils;

import java.io.File;
import java.io.IOException;
import java.util.List;

/**
 * @author Benjamin Alt
 * Handles communication with the GeTeTa verification engine
 */
public class GeTeTaVerificationEngine implements VerificationEngine {
  private GeTeTaImporter importer;
  private Process getetaProcess;
  private NullableProperty<VerificationResult> verificationResult;
  private String getetaFilename;
  private String nuxmvFilename;

  public GeTeTaVerificationEngine(String getetaFilename, String nuxmvFilename, List<Type> typeContext) {
    importer = new GeTeTaImporter(typeContext);
    verificationResult = new NullableProperty<>();
    getetaProcess = null;
    this.getetaFilename = getetaFilename;
    this.nuxmvFilename = nuxmvFilename;
  }

  @Override
  public void startVerification(VerificationScenario scenario,
                                ConstraintSpecification spec) throws
      IOException, ExportException
  {
    System.out.println("Starting verification...");
    // Write ConstraintSpecification and Code to temporary files
    File tempSpecFile = File.createTempFile("verification-spec", ".xml");
    File tempCodeFile = File.createTempFile("verification-code", ".st");
    ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.GETETA, tempSpecFile);
    ExporterFacade.exportCode(scenario.getCode(), tempCodeFile);
    // Start verification engine in new child process
    String getetaCommand = "java -jar " + getetaFilename + " -c " + tempCodeFile.getAbsolutePath() + " -t " +
        tempSpecFile.getAbsolutePath() + " -x";
    if (getetaProcess != null) {
      cancelVerification();
    }
    ProcessBuilder processBuilder = new ProcessBuilder(getetaCommand.split(" "));
    processBuilder.environment().put("NUXMV", nuxmvFilename);
    getetaProcess = processBuilder.start();
    // Find out when process finishes to set verification result property
    ProcessExitDetector exitDetector = new ProcessExitDetector(getetaProcess);
    exitDetector.processFinishedProperty().addListener(new VerificationDoneListener());
    exitDetector.start();
  }

  @Override
  public void cancelVerification() {
    System.out.println("Cancelling verification...");
    if (getetaProcess != null) {
      getetaProcess.destroy();
      getetaProcess = null;
      System.out.println("Verification cancelled.");
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
    assert getetaProcess != null;
    System.out.println("Verification done!");
    try {
      System.out.println(IOUtils.toString(getetaProcess.getInputStream(), "utf-8"));
      verificationResult.set(importer.doImport(getetaProcess.getInputStream()));
    } catch (ImportException | IOException e) {
      e.printStackTrace();
      verificationResult.set(null);
    }
  }
}
