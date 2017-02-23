package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.logic.specification.smtlib.OptionalConcreteSpecificationHandler;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.util.ThrowableHandler;
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
                                      OptionalConcreteSpecificationHandler handler,
                                      ThrowableHandler exceptionHandler);
  void terminate();
}

