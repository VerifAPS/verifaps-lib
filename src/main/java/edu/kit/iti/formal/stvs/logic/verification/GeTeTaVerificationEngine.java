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
import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import org.apache.commons.io.IOUtils;

import java.io.*;
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

  public GeTeTaVerificationEngine(String getetaFilename, String nuxmvFilename, List<Type> typeContext) throws VerificationException {
    importer = new GeTeTaImporter(typeContext);
    verificationResult = new NullableProperty<>();
    getetaProcess = null;
    this.getetaFilename = getetaFilename;
    this.nuxmvFilename = nuxmvFilename;
    /* Check filenames */
    File getetaFile = new File(getetaFilename);
    File nuxmvFile = new File(nuxmvFilename);
    if (!getetaFile.exists() || getetaFile.isDirectory()) {
      throw new VerificationException(VerificationException.Reason.GETETA_NOT_FOUND);
    }
    if (!nuxmvFile.exists() || nuxmvFile.isDirectory()) {
      throw new VerificationException(VerificationException.Reason.NUXMV_NOT_FOUND);
    }
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
    ExporterFacade.exportCode(scenario.getCode(), tempCodeFile, true);
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
    try {
      Platform.runLater(exitDetector);
    } catch (IllegalStateException e) {
      // We are not in a JavaFX environment
      exitDetector.start();
    }
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
    File logFile;
    String processOutput;
    try {
      logFile = File.createTempFile("log-verification-", ".xml");
      processOutput = IOUtils.toString(getetaProcess.getInputStream(), "utf-8");
    } catch (IOException e) {
      e.printStackTrace();
      verificationResult.set(null);
      return;
    }
    // Preprocess output (remove anything before the XML)
    String cleanedProcessOutput = cleanProcessOutput(processOutput);
    try {
      verificationResult.set(importer.doImport(new ByteArrayInputStream(cleanedProcessOutput
          .getBytes())));
    } catch (ImportException e) {
      PrintWriter writer;
      String logFilePath = logFile.getAbsolutePath();
      try {
        writer = new PrintWriter(logFilePath);
      } catch (FileNotFoundException e1) {
        e1.printStackTrace();
        verificationResult.set(null);
        return;
      }
      writer.println(processOutput);
      writer.close();
      verificationResult.set(new VerificationResult(VerificationResult.Status.ERROR, logFilePath));
    }
  }

  private String cleanProcessOutput(String processOutput) {
    int xmlStartIndex = processOutput.indexOf("<");
    return processOutput.substring(xmlStartIndex);
  }
}
