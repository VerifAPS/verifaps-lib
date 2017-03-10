package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.view.VerificationResultVisitor;

import java.io.File;
import java.util.Optional;

/**
 * A {@link VerificationResult} with a counterexample.
 * @author Benjamin Alt
 */
public class Counterexample implements VerificationResult {
  private final File logFile;
  private final ConcreteSpecification counterexample;

  /**
   * Create a new Counterexample from a given {@link ConcreteSpecification} and a log file.
   * @param counterexample The concrete specification (counterexample)
   * @param logFile The log file
   */
  public Counterexample(ConcreteSpecification counterexample, File logFile) {
    assert counterexample.isCounterExample();
    this.logFile = logFile;
    this.counterexample = counterexample;
  }

  @Override
  public void accept(VerificationResultVisitor visitor) {
    visitor.visitCounterexample(this);
  }

  @Override
  public Optional<File> getLogFile() {
    return Optional.ofNullable(logFile);
  }

  /**
   * Get the counterexample.
   * @return The counterexample
   */
  public ConcreteSpecification getCounterexample() {
    return counterexample;
  }
}
