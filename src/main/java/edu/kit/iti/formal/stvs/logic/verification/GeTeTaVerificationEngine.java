package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import javafx.application.Platform;
import org.apache.commons.io.IOUtils;

import java.io.*;
import java.util.List;

/**
 * @author Benjamin Alt
 * Handles communication with the GeTeTa verification engine
 */
public class GeTeTaVerificationEngine implements VerificationEngine {
  private Process getetaProcess;
  private NullableProperty<VerificationResult> verificationResult;
  private List<Type> typeContext;
  private GlobalConfig config;
  private File getetaOutputFile;
  private ProcessMonitor processMonitor;

  public GeTeTaVerificationEngine(GlobalConfig config, List<Type> typeContext) throws
      VerificationException {
    verificationResult = new NullableProperty<>();
    getetaProcess = null;
    this.typeContext = typeContext;
    this.config = config;
    /* Check filenames */
    File nuxmvFile = new File(config.getNuxmvFilename());
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
    String getetaCommand = config.getGetetaCommand().replace("${code}", tempCodeFile
        .getAbsolutePath()).replace("${spec}", tempSpecFile.getAbsolutePath());
    // Start verification engine in new child process
    if (getetaProcess != null) {
      cancelVerification();
    }
    ProcessBuilder processBuilder = new ProcessBuilder(getetaCommand.split(" "));
    processBuilder.environment().put("NUXMV", config.getNuxmvFilename());
    getetaOutputFile = File.createTempFile("verification-result", ".log");
    processBuilder.redirectOutput(getetaOutputFile);
    getetaProcess = processBuilder.start();
    // Find out when process finishes to set verification result property
    processMonitor = new ProcessMonitor(getetaProcess, config.getVerificationTimeout());
    processMonitor.processFinishedProperty().addListener(observable -> onVerificationDone());
    // Starts the verification process in another thread
    processMonitor.start();
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

  private void onVerificationDone() {
    if (getetaProcess == null) { // Verification was cancelled
      return;
    }
    System.out.println("Verification done!");
    File logFile;
    String processOutput;
    try {
      logFile = File.createTempFile("log-verification-", ".xml");
      processOutput = IOUtils.toString(new FileInputStream(getetaOutputFile), "utf-8");
      getetaOutputFile.delete();
    } catch (IOException e) {
      e.printStackTrace();
      verificationResult.set(null);
      return;
    }
    // Preprocess output (remove anything before the XML)
    String cleanedProcessOutput = cleanProcessOutput(processOutput);
    VerificationResult result;
    // Set the verification result depending on the GeTeTa output
    try {
      if (processMonitor.isAborted()) {
        result = makeErrorResult(processOutput, logFile, VerificationResult.Status.TIMEOUT);
      } else {
        result = ImporterFacade.importVerificationResult(new ByteArrayInputStream(cleanedProcessOutput
            .getBytes()), ImporterFacade.ImportFormat.GETETA, typeContext);
      }
    } catch (ImportException e) {
      result = makeErrorResult(processOutput, logFile, VerificationResult.Status.ERROR);
    }
    // set the verification result back in the javafx thread:
    VerificationResult finalResult = result; // have to do this because of lambda restrictions...
    Platform.runLater(() -> verificationResult.set(finalResult));
  }

  private VerificationResult makeErrorResult(String processOutput, File logFile, VerificationResult.Status
      errorStatus) {
    PrintWriter writer;
    String logFilePath = logFile.getAbsolutePath();
    try {
      writer = new PrintWriter(logFilePath);
    } catch (FileNotFoundException e1) {
      e1.printStackTrace();
      return null;
    }
    writer.println(processOutput);
    writer.close();
    return new VerificationResult(errorStatus, logFilePath);
  }

  private String cleanProcessOutput(String processOutput) {
    int xmlStartIndex = processOutput.indexOf("<");
    if (xmlStartIndex >= 0) {
      return processOutput.substring(xmlStartIndex);
    }
    return processOutput;
  }
}
