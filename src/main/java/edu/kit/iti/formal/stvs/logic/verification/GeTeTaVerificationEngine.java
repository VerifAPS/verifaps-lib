package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationError;
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
      VerificationError {
    verificationResult = new NullableProperty<>();
    getetaProcess = null;
    this.typeContext = typeContext;
    this.config = config;
    /* Check filenames */
    File nuxmvFile = new File(config.getNuxmvFilename());
    if (!nuxmvFile.exists() || nuxmvFile.isDirectory()) {
      throw new VerificationError(VerificationError.Reason.NUXMV_NOT_FOUND);
    }
  }

  @Override
  public void startVerification(VerificationScenario scenario,
                                ConstraintSpecification spec) throws
      IOException, ExportException, VerificationError {
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
    try {
      processMonitor = new ProcessMonitor(getetaProcess, config.getVerificationTimeout());
      processMonitor.processFinishedProperty().addListener(observable -> onVerificationDone());
      // Starts the verification process in another thread
      processMonitor.start();
    } catch (IllegalArgumentException e) {
      throw new VerificationError(VerificationError.Reason.VERIFICATION_LAUNCH_ERROR);
    }
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

  private void onVerificationDone() {
    if (getetaProcess == null) { // Verification was cancelled
      return;
    }
    VerificationResult result;
    File logFile = null;
    try {
      String processOutput = IOUtils.toString(new FileInputStream(getetaOutputFile), "utf-8");
      logFile = writeLogFile(processOutput);
      String cleanedProcessOutput = cleanProcessOutput(processOutput);
      // Set the verification result depending on the GeTeTa output
      if (processMonitor.isAborted()) {
        VerificationError error = new VerificationError(VerificationError.Reason.TIMEOUT);
        result = new VerificationResult(VerificationResult.Status.ERROR, logFile, error);
      } else {
        result = ImporterFacade.importVerificationResult(new ByteArrayInputStream(cleanedProcessOutput
            .getBytes()), ImporterFacade.ImportFormat.GETETA, typeContext);
      }
    } catch (IOException | ImportException e) {
      VerificationError error = new VerificationError(e);
      result = new VerificationResult(VerificationResult.Status.ERROR, logFile, error);
    }
    // set the verification result back in the javafx thread:
    VerificationResult finalResult = result; // have to do this because of lambda restrictions...
    try {
      Platform.runLater(() -> verificationResult.set(finalResult));
    } catch (IllegalStateException e) {
      verificationResult.set(finalResult);
    }
  }

  private File writeLogFile(String processOutput) throws IOException {
    File logFile = File.createTempFile("log-verification-", ".xml");
    getetaOutputFile.delete();
    String logFilePath = logFile.getAbsolutePath();
    PrintWriter writer = new PrintWriter(logFilePath);
    writer.println(processOutput);
    writer.close();
    return logFile;
  }

  private String cleanProcessOutput(String processOutput) {
    int xmlStartIndex = processOutput.indexOf("<");
    if (xmlStartIndex >= 0) {
      return processOutput.substring(xmlStartIndex);
    }
    return processOutput;
  }
}
