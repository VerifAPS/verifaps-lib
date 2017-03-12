package edu.kit.iti.formal.stvs.model.verification;

import java.io.IOException;

/**
 * A visitor for {@link VerificationResult}s.
 */
public interface VerificationResultVisitor {

  /**
   * Visit a {@link Counterexample}.
   * @param result Counterexample to visit.
   */
  void visitCounterexample(Counterexample result);

  /**
   * Visit a {@link VerificationError}.
   * @param result error to visit
   */
  void visitVerificationError(VerificationError result);

  /**
   * Visit a {@link VerificationSuccess}.
   * @param result success to visit
   */
  void visitVerificationSuccess(VerificationSuccess result);
}
