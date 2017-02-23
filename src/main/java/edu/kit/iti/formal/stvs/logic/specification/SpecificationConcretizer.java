package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.logic.specification.smtlib.OptionalConcreteSpecificationHandler;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.util.ThrowableHandler;

import java.util.List;


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

