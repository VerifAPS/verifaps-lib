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
import edu.kit.iti.formal.stvs.util.ProcessCreationException;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Optional;

import javafx.application.Platform;
import org.apache.commons.io.IOUtils;

/**
 * Handles communication with the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 */
public class GeTeTaVerificationEngine implements VerificationEngine {
  private Process getetaProcess;
  private NullableProperty<VerificationResult> verificationResult;
  private List<Type> typeContext;
  private GlobalConfig config;
  private File getetaOutputFile;
  private ProcessMonitor processMonitor;

  /**
   * Creates an instance based on given {@link GlobalConfig} and {@code typeContext}. The
   * {@code typeContext} is used later for importing the possible counterexample.
   *
   * @param config config that should be used
   * @param typeContext list of types used for importing counterexample
   * @throws FileNotFoundException nuXmv not found
   */
  public GeTeTaVerificationEngine(GlobalConfig config, List<Type> typeContext)
      throws FileNotFoundException {
    verificationResult = new NullableProperty<>();
    getetaProcess = null;
    this.typeContext = typeContext;
    this.config = config;

    /* Check if nuXmv executable exists */
    File nuxmvFile = new File(config.getNuxmvFilename());
    if (!nuxmvFile.exists() || nuxmvFile.isDirectory()) {
      throw new FileNotFoundException(
          "The NuXmv executable " + nuxmvFile.getAbsolutePath() + " could not be found.");
    }
  }

  /**
   * Exports the given {@link VerificationScenario} to temporary files and starts the GeTeTa
   * verification engine process.
   *
   * @param scenario scenario that hold the code to be checked
   * @param spec specification that should be checked
   * @throws IOException exception while creating process
   * @throws ExportException exception while exporting
   */
  @Override
  public void startVerification(VerificationScenario scenario, ConstraintSpecification spec)
      throws IOException, ExportException, ProcessCreationException {

    // Write ConstraintSpecification and Code to temporary files
    File tempSpecFile = File.createTempFile("verification-spec", ".xml");
    File tempCodeFile = File.createTempFile("verification-code", ".st");
    ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.GETETA, tempSpecFile);
    ExporterFacade.exportCode(scenario.getCode(), tempCodeFile, true);
    String getetaCommand =
        config.getGetetaCommand().replace("${code}", tempCodeFile.getAbsolutePath())
            .replace("${spec}", tempSpecFile.getAbsolutePath());

    // Start verification engine in new child process
    if (getetaProcess != null) {
      cancelVerification();
    }
    ProcessBuilder processBuilder = new ProcessBuilder(getetaCommand.split(" "));
    processBuilder.environment().put("NUXMV", config.getNuxmvFilename());
    getetaOutputFile = File.createTempFile("verification-result", ".log");
    processBuilder.redirectOutput(getetaOutputFile);
    try {
      getetaProcess = processBuilder.start();
      // Find out when process finishes to set verification result property
      processMonitor = new ProcessMonitor(getetaProcess, config.getVerificationTimeout());
      processMonitor.processFinishedProperty().addListener(observable -> onVerificationDone());
      // Starts the verification process in another thread
      processMonitor.start();
    } catch (IllegalArgumentException | ArrayIndexOutOfBoundsException exception) {
      throw new ProcessCreationException("The verification could not be launched");
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

  /**
   * Handles the output of the GeTeTa verification engine.
   */
  private void onVerificationDone() {
    if (getetaProcess == null) { // Verification was cancelled
      return;
    }
    VerificationResult result;
    File logFile = null;
    Optional<Exception> processError = processMonitor.getError();
    if (processError.isPresent()) {
      result = new VerificationError(processError.get());
    } else {
      try {
        String processOutput = IOUtils.toString(new FileInputStream(getetaOutputFile), "utf-8");
        logFile = writeLogFile(processOutput);
        String cleanedProcessOutput = cleanProcessOutput(processOutput);
        // Set the verification result depending on the GeTeTa output
        if (processMonitor.isAborted()) {
          result = new VerificationError(VerificationError.Reason.TIMEOUT, logFile);
        } else {
          result = ImporterFacade.importVerificationResult(
              new ByteArrayInputStream(cleanedProcessOutput.getBytes("utf-8")),
              ImporterFacade.ImportFormat.GETETA, typeContext);
        }
      } catch (IOException | ImportException exception) {
        result = new VerificationError(exception, logFile);
      }
    }
    // Set the verification result back in the javafx thread:
    VerificationResult finalResult = result; // have to do this because of lambda restrictions...
    try {
      Platform.runLater(() -> verificationResult.set(finalResult));
    } catch (IllegalStateException exception) {
      verificationResult.set(finalResult);
    }
  }

  private File writeLogFile(String processOutput) throws IOException {
    File logFile = File.createTempFile("log-verification-", ".xml");
    getetaOutputFile.deleteOnExit();
    PrintWriter writer = new PrintWriter(
        new OutputStreamWriter(new FileOutputStream(logFile), StandardCharsets.UTF_8), true);
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
