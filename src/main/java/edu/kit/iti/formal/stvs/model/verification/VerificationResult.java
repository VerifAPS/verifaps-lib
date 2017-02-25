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

  public Optional<VerificationError> getVerificationError() {
    return Optional.ofNullable(verificationError);
  }

  public boolean isSuccessful() {
    return status == Status.VERIFIED;
  }

  public Status getStatus() {
    return status;
  }

  public ConcreteSpecification getCounterExample() {
    return counterexample;
  }

  public Optional<File> getLogFile() {
    return Optional.ofNullable(logFile);
  }

  public enum Status { VERIFIED, COUNTEREXAMPLE, ERROR }
}
