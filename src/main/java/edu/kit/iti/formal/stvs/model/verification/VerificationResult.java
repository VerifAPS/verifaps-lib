package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;

/**
 * The result of a verification (the model equivalent of the output of a verification engine
 * (such as GeTeTa).
 * @author Benjamin Alt
 */
public class VerificationResult {

  private ConcreteSpecification counterexample;
  private Status status;
  private String logFilePath;

  /**
   * Construct a new VerificationResult for a verification without counterexample.
   * @param status The status of the verification (i.e. verified, counterexample, error, ...)
   * @param logFilePath The path to the log file (the original output of the verification engine)
   */
  public VerificationResult(Status status, String logFilePath) {
    this.status = status;
    this.logFilePath = logFilePath;
  }

  /**
   * Construct a new VerificationResult with a counterexample for an unsuccessful verification.
   * @param counterexample The counterexample
   * @param logFilePath The path to the log file (the original output of the verification engine)
   */
  public VerificationResult(ConcreteSpecification counterexample, String logFilePath) {
    this(Status.COUNTEREXAMPLE, logFilePath);
    this.counterexample = counterexample;
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

  public String getLogFilePath() {
    return logFilePath;
  }

  public enum Status { VERIFIED, COUNTEREXAMPLE, UNKNOWN, ERROR, FATAL }
}
