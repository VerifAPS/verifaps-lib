package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;

/**
 * Created by csicar on 09.01.17.
 */
public class VerificationResult {

  public boolean isSuccessful() {
    return false;
  }

  public ConcreteSpecification getCounterExample() {
    return null;
  }
}
