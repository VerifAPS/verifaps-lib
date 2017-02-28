package edu.kit.iti.formal.stvs.model.verification;

import java.util.HashMap;
import java.util.Map;

/**
 * Errors related to the verification process.
 *
 * @author Benjamin Alt
 */
public class VerificationError extends Exception {

  /* Error messages for the different error reasons */
  private static final Map<Reason, String> errorMessages;

  static {
    errorMessages = new HashMap<>();
    errorMessages.put(Reason.VERIFICATION_LAUNCH_ERROR, "The verification could not be launched. " +
        "Check the verification engine command in the preferences dialog (Edit -> Preferences)");
    errorMessages.put(Reason.NUXMV_NOT_FOUND, "The nuXmv executable could not be found. " +
        "Check the path to the nuXmv executable in the preferences dialog (Edit -> Preferences)");
    errorMessages.put(Reason.PROCESS_ABORTED, "The verification process has been aborted.");
    errorMessages.put(Reason.TIMEOUT, "The verification timed out.");
    errorMessages.put(Reason.ERROR, "An error occurred during verification.");
    errorMessages.put(Reason.UNKNOWN, "An unknown error occurred during verification.");
  }

  private Reason reason;

  /**
   * Construct a new VerificationError for a specific reason.
   *
   * @param reason The reason for the VerificationError
   */
  public VerificationError(Reason reason) {
    this.reason = reason;
  }

  /**
   * Construct a new VerificationError from an Exception (which was thrown while
   * launching/managing the verification. These will typically not come from the verification
   * engine itself).
   *
   * @param e The exception to construct a VerificationError from
   */
  public VerificationError(Exception e) {
    this.reason = Reason.EXCEPTION;
    this.setStackTrace(e.getStackTrace());
    errorMessages.put(Reason.EXCEPTION, e.getMessage());
  }

  /**
   * Get the reason for this VerificationError.
   *
   * @return The reason for this VerificationError
   */
  public Reason getReason() {
    return reason;
  }

  @Override
  public String getMessage() {
    return errorMessages.get(reason);
  }

  public enum Reason {
    VERIFICATION_LAUNCH_ERROR, NUXMV_NOT_FOUND, PROCESS_ABORTED, TIMEOUT,
    ERROR, EXCEPTION, UNKNOWN
  }
}
