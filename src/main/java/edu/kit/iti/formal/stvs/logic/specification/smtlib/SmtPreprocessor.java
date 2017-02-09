package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.List;
import java.util.Map;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtPreprocessor {

  //      Map<Row, Max. number of cycles for that row>
  private Map<Integer, Integer> maxDurations;
  private List<SpecIoVariable> ioVariables;
  private Integer numOfRows;
  private ValidSpecification specification;
  private SConstrain constrain;

  public SmtPreprocessor() {
    this.constrain = new SConstrain();
    //Step 1V
    for (SpecIoVariable ioVariable : ioVariables) {
      SpecificationColumn<Expression> column = specification.getColumnByName(ioVariable.getName());
      for (int z = 0; z < column.getCells().size(); z++ ) {
        Expression expression = column.getCells().get(z);
        ExpressionConverter converter = new ExpressionConverter(expression, z);

        for (int i = 0; i < getMaxDuration(z); i++) {
          //n_z >= i => ExpressionVisitor(z,i,...)
          constrain.addAll(
              new SList("implies",
                  new SList(">=", "n_" + z, i + ""),
                  converter.convert(i)
              )
          );
        }
      }
    }
  }

  private Expression getEntry(Integer row, SpecIoVariable ioVariable) {
    return null; //TODO: implement
  }

  private Integer getMaxDuration(int j) {
    // TODO: use globalconfig value for default value
    return maxDurations.getOrDefault(j, 5);
  }
}
