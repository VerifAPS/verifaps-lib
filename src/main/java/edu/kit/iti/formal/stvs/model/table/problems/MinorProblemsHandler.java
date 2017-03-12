package edu.kit.iti.formal.stvs.model.table.problems;


/**
 * Gets invoked by {@link InvalidIoVarProblem#tryGetValidIoVariable} if a minor problem is present
 * that does not prevent a variable from being converted to a
 * {@link edu.kit.iti.formal.stvs.model.common.ValidIoVariable} but should be handled anyways.
 */
@FunctionalInterface
public interface MinorProblemsHandler {
  /**
   * Must implement a handler for minor problems while converting.
   *
   * @param minorProblem The problem which occurred while converting a
   *        {@link edu.kit.iti.formal.stvs.model.common.SpecIoVariable} to a
   *        {@link edu.kit.iti.formal.stvs.model.common.ValidIoVariable}
   */
  void handle(InvalidIoVarProblem minorProblem);
}
