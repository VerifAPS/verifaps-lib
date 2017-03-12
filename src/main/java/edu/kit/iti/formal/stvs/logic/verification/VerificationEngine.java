package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationError;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import edu.kit.iti.formal.stvs.util.ProcessCreationException;

import java.io.IOException;
import java.util.Optional;

/**
 * Strategy for verification of the VerificationScenario.
 *
 * @author Benjamin Alt
 */
public interface VerificationEngine {

  /**
   * Starts a verification in its own thread.
   *
   * @param scenario scenario that hold the code to be checked
   * @param spec specification that should be checked
   * @throws IOException exception while creating process
   * @throws ExportException exception while exporting
   * @throws ProcessCreationException exception while creating a process for verification
   */
  void startVerification(VerificationScenario scenario, ConstraintSpecification spec)
      throws IOException, ExportException, ProcessCreationException;

  NullableProperty<VerificationResult> verificationResultProperty();

  VerificationResult getVerificationResult();

  /**
   * Get the last specification for which a verification was triggered. This will return a deep
   * copy: Modifying the original {@link ConstraintSpecification} between calling
   * startVerification() and getCurrentSpec() will have no effect on the return value.
   * @return The last specification for which a verification was triggered
   */
  Optional<ConstraintSpecification> getCurrentSpec();

  /**
   * Cancels a running verification.
   */
  void cancelVerification();
}
