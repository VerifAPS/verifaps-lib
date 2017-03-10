package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.view.VerificationResultVisitor;

import java.io.File;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

/**
 * Errors related to the verification process.
 *
 * @author Benjamin Alt
 */
public class VerificationError implements VerificationResult {

  /* Error messages for the different error reasons */
  private static final Map<Reason, String> errorMessages;

  static {
    errorMessages = new HashMap<>();
    errorMessages.put(Reason.VERIFICATION_LAUNCH_ERROR, "The verification could not be launched. "
        + "Check the verification engine command in the preferences dialog (Edit -> Preferences)");
    errorMessages.put(Reason.NUXMV_NOT_FOUND, "The nuXmv executable could not be found. "
        + "Check the path to the nuXmv executable in the preferences dialog (Edit -> Preferences)");
    errorMessages.put(Reason.PROCESS_ABORTED, "The verification process has been aborted.");
    errorMessages.put(Reason.TIMEOUT, "The verification timed out.");
    errorMessages.put(Reason.ERROR, "An error occurred during verification.");
    errorMessages.put(Reason.UNKNOWN, "An unknown error occurred during verification.");
  }

  private final Reason reason;
  private File logFile;

  /**
   * Construct a new VerificationError for a specific reason.
   *
   * @param reason The reason for the VerificationError
   */
  public VerificationError(Reason reason) {
    this.reason = reason;
    this.logFile = null;
  }

  /**
   * Construct a new VerificationError for a specific reason with a given log file.
   * @param reason The reason for the VerificationError
   * @param logFile The log file
   */
  public VerificationError(Reason reason, File logFile) {
    this(reason);
    this.logFile = logFile;
  }

  /**
   * Construct a new VerificationError from an Exception (which was thrown while launching/managing
   * the verification. These will typically not come from the verification engine itself).
   *
   * @param ex The exception to construct a VerificationError from
   */
  public VerificationError(Exception ex) {
    this.reason = Reason.EXCEPTION;
    try {
      logFile = File.createTempFile("verification-exception", "");
      PrintWriter printWriter = new PrintWriter(logFile);
      ex.printStackTrace(printWriter);
    } catch (Exception exception) {
      // Do nothing if writing the exception to the log throws an exception
      logFile = null;
    }
    errorMessages.put(Reason.EXCEPTION, ex.getMessage());
  }

  public VerificationError(Exception ex, File logFile) {
    this.reason = Reason.EXCEPTION;
    this.logFile = logFile;
    errorMessages.put(Reason.EXCEPTION, ex.getMessage());
  }

  /**
   * Get an error message describing the error.
   * @return An error message describing the error
   */
  public String getMessage() {
    return errorMessages.get(reason);
  }

  @Override
  public void accept(VerificationResultVisitor visitor) {
    visitor.visitVerificationError(this);
  }

  @Override
  public Optional<File> getLogFile() {
    return Optional.ofNullable(logFile);
  }

  /**
   * Reasons why a {@link VerificationError} may occur.
   */
  public enum Reason {
    VERIFICATION_LAUNCH_ERROR, NUXMV_NOT_FOUND, PROCESS_ABORTED, TIMEOUT, ERROR, EXCEPTION, UNKNOWN
  }
}
