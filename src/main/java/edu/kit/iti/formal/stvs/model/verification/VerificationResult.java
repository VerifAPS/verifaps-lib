package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;

/**
 * @author Benjamin Alt
 */
public class VerificationResult {

  private ConcreteSpecification counterexample;
  private boolean successful;

  /**
   * Construct a new VerificationResult for a successful verification.
   */
  public VerificationResult() {
    successful = true;
  }

  /**
   * Construct a new VerificationResult with a counterexample for an unsuccessful verification
   * @param counterexample
   */
  public VerificationResult(ConcreteSpecification counterexample) {
    this.counterexample = counterexample;
    successful = false;
  }

  public boolean isSuccessful() {
    return successful;
  }

  public ConcreteSpecification getCounterExample() {
    return counterexample;
  }
}
