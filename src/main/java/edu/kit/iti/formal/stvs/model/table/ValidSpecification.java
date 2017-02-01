package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.Map;
import java.util.Set;

/**
 * @author Benjamin Alt
 */
public class ValidSpecification extends SpecificationTable<Expression, LowerBoundedInterval> {

  private final Set<Type> typeContext;
  private FreeVariableSet freeVariableSet;

  public ValidSpecification(Map<String, SpecificationColumn<Expression>> columns, Map<Integer,LowerBoundedInterval> durations,
                            Set<Type> typeContext, FreeVariableSet freeVariableSet) {
    super(columns, durations);
    this.typeContext = typeContext;
    this.freeVariableSet = freeVariableSet;
  }
}
