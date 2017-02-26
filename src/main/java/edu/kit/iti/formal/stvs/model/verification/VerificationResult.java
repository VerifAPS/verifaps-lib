package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;

import java.io.File;
import java.util.Optional;

/**
 * The result of a verification (created by a
 * {@link edu.kit.iti.formal.stvs.logic.verification.VerificationEngine}).
 * @author Benjamin Alt
 */
public class VerificationResult {

  private ConcreteSpecification counterexample;
  private Status status;
  private File logFile;
  private VerificationError verificationError;

  /**
   * Construct a new VerificationResult for a verification without counterexample.
   * @param status The status of the verification (i.e. verified, counterexample, error, ...)
   * @param logFile The log file (the original output of the verification engine)
   */
  public VerificationResult(Status status, File logFile, VerificationError error) {
    this.status = status;
    this.logFile = logFile;
    this.verificationError = error;
  }

  /**
   * Construct a new VerificationResult with a counterexample for an unsuccessful verification.
   * @param counterexample The counterexample
   * @param logFile The log file (the original output of the verification engine)
   */
  public VerificationResult(ConcreteSpecification counterexample, File logFile) {
    this(Status.COUNTEREXAMPLE, logFile, null);
    this.counterexample = counterexample;
  }

  /**
   * Get the current verification error or an empty Optional if none occurred.
   * @return The current verification error or an empty Optional if none occurred
   */
  public Optional<VerificationError> getVerificationError() {
    return Optional.ofNullable(verificationError);
  }

  /**
   * Get the status of the verification.
   * @return The current verification status
   */
  public Status getStatus() {
    return status;
  }

  /**
   * Get the counterexample or an empty Optional if none is available.
   * @return The counterexample or an empty Optional if none is available
   */
  public Optional<ConcreteSpecification> getCounterExample() {
    return Optional.ofNullable(counterexample);
  }

  /**
   * Get the log file or an empty Optional if none is available. This would be the case for some
   * verification errors (such as IOExceptions).
   * @return The log file or an empty Optional if none is available
   */
  public Optional<File> getLogFile() {
    return Optional.ofNullable(logFile);
  }

  /**
   * The verification status.
   */
  public enum Status { VERIFIED, COUNTEREXAMPLE, ERROR }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    VerificationResult result = (VerificationResult) o;

    if (counterexample != null ? !counterexample.equals(result.counterexample) : result.counterexample != null)
      return false;
    if (getStatus() != result.getStatus()) return false;
    if (getLogFile() != null ? !getLogFile().equals(result.getLogFile()) : result.getLogFile() != null)
      return false;
    return getVerificationError() != null ? getVerificationError().equals(result.getVerificationError()) : result.getVerificationError() == null;
  }
}
