package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import org.apache.commons.lang3.tuple.Pair;

import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;


/**
 * @author Benjamin Alt
 */
public interface SpecificationConcretizer {

  void calculateConcreteSpecification(ValidSpecification validSpecification,
                                      List<ValidFreeVariable> freeVariables,
                                      Consumer<Optional<ConcreteSpecification>> consumer,
                                      Consumer<Throwable> exceptionHandler);
  void terminate();
}

