package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;

import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created by leonk on 22.02.2017.
 */
public interface OptionalConcreteSpecificationHandler extends Consumer<Optional<ConcreteSpecification>> {
  /**
   * Performs this operation on the given concreteSpecification.
   *
   * @param optionalConcreteSpecification the concreteSpecification argument
   */
  @Override
  public void accept(Optional<ConcreteSpecification> optionalConcreteSpecification);
}
