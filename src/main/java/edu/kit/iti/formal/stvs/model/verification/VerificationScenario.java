package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.logic.verification.VerificationEngine;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

/**
 * Created by csicar on 09.01.17.
 */
public class VerificationScenario {
  private VerificationResult verificationResult;
  private VerificationEngine verificationEngine;
  private Code code;

  public void verify(ConstraintSpecification spec) {

  }

  public void cancel() {

  }

  public void addOnVerificationStoppedListener() {

  }

  public VerificationState getVerificationState() {
    return null;
  }
}
