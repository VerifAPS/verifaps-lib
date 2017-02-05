package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * @author Benjamin Alt
 */
public class ValidSpecification extends SpecificationTable<Expression, LowerBoundedInterval> {

  private final ObservableSet<Type> typeContext;
  private FreeVariableSet freeVariableSet;

  public ValidSpecification(ObservableSet<Type> typeContext, FreeVariableSet freeVariableSet) {
    super();
    this.typeContext = typeContext;
    this.freeVariableSet = freeVariableSet;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    ValidSpecification that = (ValidSpecification) o;

    if (typeContext != null ? !typeContext.equals(that.typeContext) : that.typeContext != null)
      return false;
    return freeVariableSet != null ? freeVariableSet.equals(that.freeVariableSet) : that.freeVariableSet == null;
  }

  @Override
  public int hashCode() {
    int result = typeContext != null ? typeContext.hashCode() : 0;
    result = 31 * result + (freeVariableSet != null ? freeVariableSet.hashCode() : 0);
    return result;
  }
}
