package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.Set;

/**
 * @author Benjamin Alt
 */
public class ValidSpecification extends SpecificationTable<Expression, LowerBoundedInterval> {

  private final Set<Type> typeContext;
  private Set<SpecIoVariable> specIoVariables;
  private FreeVariableSet freeVariableSet;

  public ValidSpecification(Set<Type> typeContext) {
    super();
    this.typeContext = typeContext;
  }
}
