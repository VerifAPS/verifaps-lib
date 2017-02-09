package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtPreprocessor {

  private static Map<String, String> smtlibTypes = new HashMap<String,
      String>() {{
    put("INT", "Int");
    put("BOOL", "Bool");
  }};
  //      Map<Row, Max. number of cycles for that row>
  private final Map<Integer, Integer> maxDurations;
  private final List<SpecIoVariable> ioVariables;
  private final ValidSpecification specification;
  private final Map<String, Type> typeContext;
  private final Predicate<Type> isIoVariable;
  private SConstraint sConstrain;

  public SmtPreprocessor(Map<Integer, Integer> maxDurations, List<SpecIoVariable> ioVariables,
                         ValidSpecification specification, Map<String, Type> typeContext, Predicate<Type> isIoVariable) {
    this.maxDurations = maxDurations;
    this.ioVariables = ioVariables;
    this.specification = specification;
    this.typeContext = typeContext;
    this.isIoVariable = isIoVariable;
    this.sConstrain = new SConstraint()
        .addVariableDefinitions(createEnumTypes());

    //Step I, II, IV
    for (SpecIoVariable ioVariable : this.ioVariables) {
      SpecificationColumn<Expression> column = this.specification.getColumnByName(ioVariable.getName());
      for (int z = 0; z < column.getCells().size(); z++ ) {
        Expression expression = column.getCells().get(z);
        ExpressionConverter converter = new ExpressionConverter(expression, z);

        for (int i = 0; i < getMaxDuration(z); i++) {
          RecSConstraint expressionConstraint = converter.convert(i);
          //n_z >= i => ExpressionVisitor(z,i,...)
          this.sConstrain = new RecSConstraint(
              new SList("implies",
                new SList(">=", "n_" + z, i + ""),
                expressionConstraint.getRecExpression()
              ),
              expressionConstraint.getGlobalConstraints(),
              expressionConstraint.getVariableDefinitions()
          ).combine(this.sConstrain);
        }
      }
    }

    //Step III neg. Indizes verbinden
    for (SpecIoVariable ioVariable : this.ioVariables) {
      SpecificationColumn<Expression> column = this.specification.getColumnByName(ioVariable.getName());
      String variableName = ioVariable.getName();
      for (int z = 0; z < column.getCells().size(); z++ ) {
        Expression expression = column.getCells().get(z);

        for (int i = 1; i < getMaxDurationSum(z - 1); i++) {
          for (int k = 0; k < getMaxDuration(z - 1); k++) {
            // n_(z-1) = k => A_z_i = A_(z-1)_(k-i)
            this.sConstrain.addGlobalConstrains(
                new SList("implies",
                    new SList("=",
                        "n_" + (z - 1),
                        k + ""
                    ),
                    new SList("=",
                        variableName + "_" + z + "_" + (-i),
                        variableName + "_" + (z - 1) + "_" + (k - i)
                    )
                )
            );
          }
        }
      }
    }
  }

  private List<SExpr> createFreeVariables() {
    return typeContext.entrySet().stream()
        .filter(item -> !isIoVariable.test(item.getValue()))
        .map(item -> {
      String typeName = item.getValue().getTypeName();
      String variableName = item.getKey();
      return new SList("declare-const", variableName, getSMTLibVariableTypeName(typeName));
    }).collect(Collectors.toList());
  }


  private List<SExpr> createEnumTypes() {
    return typeContext.entrySet().stream().map(item -> {
      String typeName = item.getValue().getTypeName();
      List<ValueEnum> valueEnums = item.getValue().match(
          LinkedList::new,
          LinkedList::new,
          TypeEnum::getValues
      );
      List<String> arguments = valueEnums.stream().map(ValueEnum::getValueString).collect(Collectors.toList());
      /*
      (declare-datatypes () ((Color red green blue)))
       */
      return new SList("declare-datatypes", new SList(), new SList(
          (new SList(typeName)).addListElements(arguments)
      ));
    }).collect(Collectors.toList());
  }

  private String getSMTLibVariableTypeName(String typeName) {
    return smtlibTypes.getOrDefault(typeName, typeName);
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
