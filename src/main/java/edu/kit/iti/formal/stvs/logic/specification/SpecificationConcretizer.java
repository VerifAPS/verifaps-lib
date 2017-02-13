package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import javafx.beans.property.ObjectProperty;

import java.io.IOException;
import java.util.Optional;
import java.util.function.Consumer;


/**
 * @author Benjamin Alt
 */
public interface SpecificationConcretizer {

  Optional<ConcreteSpecification> calculateConcreteSpecification() throws IOException;

  /**
   * returns the previously calculated concretespecification
   * ! calling this method without successfully calculating a concrete specification first will
   * <i>always</i> return Optional.empty()
   * @return the concretized specification, if available
   */
  Optional<ConcreteSpecification> getConcreteSpecification();

  void addEventListener(Consumer<SpecificationConcretizerState> eventListener);
}

