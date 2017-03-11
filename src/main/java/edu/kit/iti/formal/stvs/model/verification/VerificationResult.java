package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.view.VerificationResultVisitor;

import java.io.File;
import java.util.Optional;

/**
 * The result of a verification (created by a
 * {@link edu.kit.iti.formal.stvs.logic.verification.VerificationEngine}).
 *
 * @author Benjamin Alt
 */
public interface VerificationResult {

  /**
   * Accept a visitor.
   * @param visitor The visitor to visit this VerificationResult
   */
  void accept(VerificationResultVisitor visitor);

  /**
   * Get the log file (containing the output of the verification engine) or an empty Optional if
   * none is available. This would be the case if certain verification errors (such as
   * IOExceptions) occurred.
   *
   * @return The log file or an empty Optional if none is available
   */
  Optional<File> getLogFile();
}
