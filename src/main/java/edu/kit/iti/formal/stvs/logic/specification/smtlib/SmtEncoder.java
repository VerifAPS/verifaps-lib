package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.automation.datatypes.Int;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtEncoder {
  //      Map<Row, Max. number of cycles for that row>
  private final Function<Integer, Integer> maxDurations;
  private final List<ValidIoVariable> ioVariables;
  private final ValidSpecification specification;
  private final Predicate<String> isIoVariable;
  private final Map<String, Type> freeVariablesContext;
  private final List<ValidFreeVariable> validFreeVariables;

  private SConstraint sConstrain;

  public SmtEncoder(Map<Integer, Integer> maxDuration, ValidSpecification specification,
                    List<ValidFreeVariable> validFreeVariables) {
    // TODO: use globalconfig value for default value
    this((pos) -> maxDuration.getOrDefault(pos, 50), specification, validFreeVariables);
  }

  public SmtEncoder(Function<Integer, Integer> maxDurations,
                    ValidSpecification specification, List<ValidFreeVariable> validFreeVariables) {
    this.maxDurations = maxDurations;
    this.specification = specification;
    this.ioVariables = specification.getColumnHeaders();
    this.validFreeVariables = validFreeVariables;
    this.freeVariablesContext = validFreeVariables.stream()
        .collect(Collectors.toMap(ValidFreeVariable::getName, ValidFreeVariable::getType));
    List<String> ioVariableTypes = ioVariables.stream().map(ValidIoVariable::getName).collect
        (Collectors.toList());

    this.isIoVariable = ioVariableTypes::contains;
    System.out.println(setFreeVariablesDefaultValues());
    this.sConstrain = new SConstraint()
        .addHeaderDefinitions(createFreeVariables())
        .addHeaderDefinitions(setFreeVariablesDefaultValues());

    System.out.println("Doing Step V");
    //Step V: upper und lower Bound von Durations festlegen
    for (int z = 0; z < specification.getDurations().size(); z++) {
      LowerBoundedInterval interval = specification.getDurations().get(z);
      //n_z >= lowerBound_z
      this.sConstrain.addGlobalConstrains(new SList("bvuge", "n_" + z, BitvectorUtils.hexFromInt(interval.getLowerBound(), 4) +
          ""));
      //n_z <= upperBound_z
      if (interval.getUpperBound().isPresent()) {
        this.sConstrain.addGlobalConstrains(new SList("bvule", "n_" + z,
            BitvectorUtils.hexFromInt(Math.min(interval.getUpperBound().get(), getMaxDuration(z)), 4)));
      } else {
        this.sConstrain.addGlobalConstrains(new SList("bvule", "n_" + z,
            BitvectorUtils.hexFromInt(getMaxDuration(z), 4)));
      }
    }

    System.out.println("doing recursive step");
    //Step I, II, IV
    for (ValidIoVariable ioVariable : this.ioVariables) {
      SpecificationColumn<Expression> column = this.specification.getColumnByName(ioVariable.getName());
      for (int z = 0; z < column.getCells().size(); z++) {
        Expression expression = column.getCells().get(z);

        for (int i = 0; i < getMaxDuration(z); i++) {
          SmtConvertExpressionVisitor visitor = new SmtConvertExpressionVisitor
              (this::getTypeForVariable, z,
                  i, ioVariable, isIoVariable, this::getSMTLibVariableTypeName);
          SExpr expressionConstraint = expression.takeVisitor(visitor);
          //n_z >= i => ExpressionVisitor(z,i,...)
          this.sConstrain = new RecSConstraint(
              new SList("implies",
                  new SList("bvuge", "n_" + z, BitvectorUtils.hexFromInt(i,4)),
                  expressionConstraint
              ),
              visitor.getConstraint().getGlobalConstraints(),
              visitor.getConstraint().getVariableDefinitions()
          ).combine(this.sConstrain);
        }
      }
    }

    System.out.println("Doing step III");
    //Step III neg. Indizes verbinden
    for (ValidIoVariable ioVariable : this.ioVariables) {
      SpecificationColumn<Expression> column = this.specification.getColumnByName(ioVariable.getName());
      String variableName = ioVariable.getName();
      //Iterate over Rows
      for (int z = 0; z < column.getCells().size(); z++) {
        Expression expression = column.getCells().get(z);
        //Add n_x to const declaration
        this.sConstrain.addHeaderDefinitions(new SList(
            "declare-const",
            "n_" + z,
            "(_ BitVec 16)"
        ));
        //Iterate over potential backward steps
        for (int i = 1; i <= getMaxDurationSum(z - 1); i++) {
          //Iterate over possible cycles in last row
          for (int k = 0; k <= getMaxDuration(z - 1); k++) {
            // n_(z-1) = k => A_z_i = A_(z-1)_(k-i)
            this.sConstrain.addGlobalConstrains(
                new SList("implies",
                    new SList("=",
                        "n_" + (z - 1),
                        BitvectorUtils.hexFromInt(k, 4)
                    ),
                    new SList("=",
                        "|" + variableName + "_" + z + "_" + (-i) + "|",
                        "|" + variableName + "_" + (z - 1) + "_" + (k - i) + "|"
                    )
                )
            );
            //Add backward reference to const declaration
            this.sConstrain.addHeaderDefinitions(
                new SList(
                    "declare-const",
                    "|" + variableName + "_" + (z - 1) + "_" + (k - i) + "|", getSMTLibVariableTypeName(ioVariable.getValidType())
                )
            );
          }
          //Add backward reference to const declaration
          this.sConstrain.addHeaderDefinitions(
              new SList(
                  "declare-const",
                  "|" + variableName + "_" + z + "_" + (-i) + "|", getSMTLibVariableTypeName(ioVariable.getValidType())
              )
          );
        }
      }
    }
  }

  private List<SExpr> setFreeVariablesDefaultValues() {
    return validFreeVariables.stream()
        .filter(variable -> variable.getDefaultValue() != null)
        .map(variable -> {
      String name = variable.getName();
      Value defaultValue = variable.getDefaultValue();
      return defaultValue.match(
          (integerVal) -> new SList(
              "=",
              "|" + variable.getName() + "|",
              BitvectorUtils.hexFromInt(integerVal, 4)),
          (boolVal) -> new SList(
              "=",
              "|" + variable.getName() + "|",
              boolVal ? "true" : "false"),
          enumVal -> new SList(
              "=",
              "|" + variable.getName() + "|",
              BitvectorUtils.hexFromInt(enumVal.getType().getValues().indexOf(enumVal), 4))
      );
    }).collect(Collectors.toList());
  }

  private Type getTypeForVariable(String variableName) {
    Type type = freeVariablesContext.get(variableName);
    if (type == null) {
      type = specification.getColumnHeaderByName(variableName).getValidType();
    }
    return type;
  }

  private List<SExpr> createFreeVariables() {
    return freeVariablesContext.entrySet().stream()
        .filter(item -> !isIoVariable.test(item.getKey()))
        .map(item -> {
          Type type = item.getValue();
          String variableName = item.getKey();
          return new SList("declare-const", "|" + variableName + "|", getSMTLibVariableTypeName(type));
        }).collect(Collectors.toList());
  }

  private String getSMTLibVariableTypeName(Type type) {
    return type.match(
        () -> "(_ BitVec 16)",
        () -> "Bool",
        e -> "(_ BitVec 16)"
    );
  }

  private int getMaxDurationSum(int z) {
    int sum = 0;
    for (int i = 0; i <= z; i++) {
      sum += getMaxDuration(i);
    }

    return sum;
  }

  private Integer getMaxDuration(int j) {
    if (j < 0) return 0;
    Optional<Integer> interval = specification.getDurations().get(j).getUpperBound();

    if(interval.isPresent()) {
      return Math.min(maxDurations.apply(j), interval.get());
    } else {
      return maxDurations.apply(j);
    }
  }

  public SConstraint getConstrain() {
    return sConstrain;
  }
}
