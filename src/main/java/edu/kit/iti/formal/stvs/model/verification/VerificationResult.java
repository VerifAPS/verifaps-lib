package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;

/**
 * @author Benjamin Alt
 */
public class VerificationResult {

  private ConcreteSpecification counterexample;
  private Status status;
  private String logFilePath;

  /**
   * Construct a new VerificationResult for a verification without counterexample.
   */
  public VerificationResult(Status status, String logFilePath) {
    this.status = status;
    this.logFilePath = logFilePath;
  }

  /**
   * Construct a new VerificationResult with a counterexample for an unsuccessful verification
   * @param counterexample
   * @param logFilePath
   */
  public VerificationResult(ConcreteSpecification counterexample, String logFilePath) {
    this(Status.COUNTEREXAMPLE, logFilePath);
    this.counterexample = counterexample;
  }

  public boolean isSuccessful() {
    return status == Status.COUNTEREXAMPLE;
  }

  public Status getStatus() {
    return status;
  }

  public ConcreteSpecification getCounterExample() {
    return counterexample;
  }

  public String getLogFilePath() {
    return logFilePath;
  }

  public enum Status { VERIFIED, COUNTEREXAMPLE, UNKNOWN, ERROR, FATAL }
}
