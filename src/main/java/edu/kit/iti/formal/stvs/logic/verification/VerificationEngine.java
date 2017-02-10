package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.IOException;

/**
 * Strategy for Verification of the VerificationScenario
 * @author Benjamin Alt
 */
public interface VerificationEngine {

  /**
   * Starts a verification in its own thread
   *
   * @param scenario scenario that should be checked
   */
  public void startVerification(VerificationScenario scenario, ConstraintSpecification spec) throws
      IOException, ExportException;

  public NullableProperty<VerificationResult> verificationResultProperty();

  public VerificationResult getVerificationResult();

  public void cancelVerification();
}
