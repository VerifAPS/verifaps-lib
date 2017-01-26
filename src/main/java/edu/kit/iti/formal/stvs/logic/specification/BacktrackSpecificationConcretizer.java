package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.Stack;
import java.util.function.Consumer;

/**
 * Created by bal on 09.01.17.
 */
public class BacktrackSpecificationConcretizer extends SpecificationConcretizer {
  private ConcretizerContext context;
  private ConcreteSpecification concreteSpecification;
  private ValidSpecification validSpecification;
  private Stack<RowSolver> rowSolverStack;

  @Override
  public void createConcreteSpecification(ValidSpecification spec) {

  }
}
