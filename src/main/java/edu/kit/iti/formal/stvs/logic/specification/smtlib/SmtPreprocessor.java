package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtPreprocessor {

  //      Map<Row, Max. number of cycles for that row>
  private Map<Integer, Integer> maxDurations;
  private List<SpecIoVariable> ioVariables;
  private Integer numOfRows;
  private ValidSpecification specification;
  private SConstrain sConstrain;

  public SmtPreprocessor() {
    this.sConstrain = new SConstrain();
    //Step I, II, IV
    for (SpecIoVariable ioVariable : ioVariables) {
      SpecificationColumn<Expression> column = specification.getColumnByName(ioVariable.getName());
      for (int z = 0; z < column.getCells().size(); z++ ) {
        Expression expression = column.getCells().get(z);
        ExpressionConverter converter = new ExpressionConverter(expression, z);

        for (int i = 0; i < getMaxDuration(z); i++) {
          SConstrain expressionConstraint = converter.convert(i);
          //n_z >= i => ExpressionVisitor(z,i,...)
          this.sConstrain.addAllUserConditions(
              new SList("implies",
                  new SList(">=", "n_" + z, i + ""),
                  expressionConstraint.getUserConditionAsSingleExpression()
              )
          );
          this.sConstrain.addAllSideConditions(expressionConstraint.getSideConditions());
          this.sConstrain.addAllVariableDefinitions(expressionConstraint.getVariableDefinitions());
        }
      }
    }

    //Step III
    for (SpecIoVariable ioVariable : ioVariables) {
      SpecificationColumn<Expression> column = specification.getColumnByName(ioVariable.getName());
      String variableName = ioVariable.getName();
      for (int z = 0; z < column.getCells().size(); z++ ) {
        Expression expression = column.getCells().get(z);

        for (int i = 1; i < getMaxDurationSum(z - 1); i++) {
          for (int k = 0; k < getMaxDuration(z - 1); k++) {
            // A_z,i
            this.sConstrain.addAllSideConditions(
                new SList("implies",
                    new SList("=",
                        "n_" + (z - 1),
                        k + ""
                    ),
                    new SList("=",
                        variableName + "_" + z + "_" + (-i),
                        variableName + "_" + (z - 1) + "_" + (k - i))
                    )
            );
          }
        }
      }
    }
  }

  private int getMaxDurationSum(int z) {
    return IntStream.range(0, z).map(this::getMaxDuration).sum();
  }

  private Expression getEntry(Integer row, SpecIoVariable ioVariable) {
    return null; //TODO: implement
  }

  private Integer getMaxDuration(int j) {
    if(j < 0) return 0;
    // TODO: use globalconfig value for default value
    return maxDurations.getOrDefault(j, 5);
  }
}
