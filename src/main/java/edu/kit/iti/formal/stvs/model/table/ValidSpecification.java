package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import javafx.beans.Observable;

/**
 * @author Benjamin Alt
 */
public class ValidSpecification extends SpecificationTable<ValidIoVariable, Expression, LowerBoundedInterval> {

  public ValidSpecification() {
    super(p -> new Observable[0], p -> new Observable[0]);
  }

}
