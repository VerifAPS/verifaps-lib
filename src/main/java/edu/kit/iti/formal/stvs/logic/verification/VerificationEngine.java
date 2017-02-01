package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

//import edu.kit.iti.formal.automation.testtables; //TODO this doesn't import despite Maven repo

/**
 * Strategy for Verification of the VerificationScenario
 */
public interface VerificationEngine {

  /**
   * Starts a verification in its own thread
   *
   * @param scenario scenario that should be checked
   */
  public void startVerification(VerificationScenario scenario);

  public OptionalProperty<VerificationResult> getVerificationResultProperty();

  public VerificationResult getVerificationResult();

  public void cancelVerification();
}
