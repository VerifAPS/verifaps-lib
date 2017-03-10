package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.view.VerificationResultVisitor;

import java.io.File;
import java.util.Optional;

/**
 * A {@link VerificationResult} indicating a successful verification (i.e. the code verified
 * against the specification).
 * @author Benjamin Alt
 */
public class VerificationSuccess implements VerificationResult {

  private final File logFile;

  public VerificationSuccess(File logFile) {
    this.logFile = logFile;
  }

  @Override
  public void accept(VerificationResultVisitor visitor) {
    visitor.visitVerificationSuccess(this);
  }

  @Override
  public Optional<File> getLogFile() {
    return Optional.ofNullable(logFile);
  }
}
