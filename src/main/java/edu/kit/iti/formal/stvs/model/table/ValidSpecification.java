package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import javafx.beans.Observable;

/**
 * A specification table that has been validated (is free from {@link SpecProblem}s) and can be
 * concretized (by a {@link edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer}).
 *
 * @author Benjamin Alt
 */
public class ValidSpecification extends SpecificationTable<ValidIoVariable, Expression, LowerBoundedInterval> {

  /**
   * Create a new empty ValidSpecification.
   */
  public ValidSpecification() {
    super(p -> new Observable[0], p -> new Observable[0]);
  }

}
