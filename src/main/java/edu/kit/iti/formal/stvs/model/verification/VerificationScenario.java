package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.logic.verification.VerificationEngine;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

/**
 * @author Benjamin Alt
 */
public class VerificationScenario {
  private VerificationResult verificationResult;
  private VerificationEngine verificationEngine;
  private Code code;

  public VerificationScenario() {
    code = new Code();
  }

  public VerificationScenario(Code code) {
    this.code = code;
  }

  public void verify(ConstraintSpecification spec) {

  }

  public void cancel() {

  }

  public void addOnVerificationStoppedListener() {

  }

  public VerificationState getVerificationState() {
    return null;
  }

  public Code getCode() {
    return code;
  }

  public void setCode(Code code) {
    this.code = code;
  }
}
