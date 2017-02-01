package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import javafx.beans.property.SimpleObjectProperty;

import java.util.Stack;

/**
 * Created by bal on 09.01.17.
 */
public class BacktrackSpecificationConcretizer implements SpecificationConcretizer {
  private ConcretizerContext context;
  private OptionalProperty<ConcreteSpecification> concreteSpecification;
  private Stack<RowSolver> rowSolverStack;

  public BacktrackSpecificationConcretizer(ConcretizerContext context) {
    this.context = context;
    this.rowSolverStack = new Stack<RowSolver>();
    this.concreteSpecification = new OptionalProperty<>(new SimpleObjectProperty<ConcreteSpecification>());
  }

  @Override
  public ConcretizerContext getContext() {
    return context;
  }

  @Override
  public void setContext(ConcretizerContext context) {
    this.context = context;
  }

  public void createConcreteSpecification(ValidSpecification spec) {

  }

  @Override
  public ConcreteSpecification getConcreteSpec() {
    return concreteSpecification.get();
  }

  @Override
  public OptionalProperty<ConcreteSpecification> concreteSpecProperty() {
    return concreteSpecification;
  }

  @Override
  public void setConcreteSpec(ConcreteSpecification concreteSpec) {
    this.concreteSpecification.set(concreteSpec);
  }
}
