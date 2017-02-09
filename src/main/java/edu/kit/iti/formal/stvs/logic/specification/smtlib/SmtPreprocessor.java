package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.*;
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
  private final Predicate<Type> isIoVariable;
  private final Map<String, Type> freeVariablesContext;

  private SConstraint sConstrain;

  public SmtPreprocessor(Map<Integer, Integer> maxDurations,
                         ValidSpecification specification) {
    this.maxDurations = maxDurations;
    this.specification = specification;
    this.ioVariables = specification.getSpecIoVariables();
    this.freeVariablesContext = specification.getFreeVariableSet().getVariableContext();
    this.isIoVariable = ioVariables::contains;
    this.sConstrain = new SConstraint()
        .addHeaderDefinitions(createEnumTypes())
        .addHeaderDefinitions(createFreeVariables());

    //Step I, II, IV
    for (SpecIoVariable ioVariable : this.ioVariables) {
      SpecificationColumn<Expression> column = this.specification.getColumnByName(ioVariable.getName());
      for (int z = 0; z < column.getCells().size(); z++ ) {
        Expression expression = column.getCells().get(z);

        for (int i = 0; i < getMaxDuration(z); i++) {
          SmtConvertExpressionVisitor visitor = new SmtConvertExpressionVisitor
              (this::getTypeForVariable, z,
              i, ioVariable, isIoVariable, this::getSMTLibVariableTypeName);
          SExpr expressionConstraint = expression.takeVisitor(visitor);
          //n_z >= i => ExpressionVisitor(z,i,...)
          this.sConstrain = new RecSConstraint(
              new SList("implies",
                new SList(">=", "n_" + z, i + ""),
                expressionConstraint
              ),
              visitor.getConstraint().getGlobalConstraints(),
              visitor.getConstraint().getVariableDefinitions()
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

    //Step V: upper und lower Bound von Durations festlegen
    for (int z = 0; z < specification.getDurations().size(); z++ ) {
      LowerBoundedInterval interval = specification.getDurations().get(z);
      this.sConstrain.addGlobalConstrains(new SList(">=", "n_" + z, interval.getLowerBound() +
          ""));
      if(interval.getUpperBound().isPresent()) {
        this.sConstrain.addGlobalConstrains(new SList("<=", "n_" + z, interval.getLowerBound() + ""));
      }
    }

  }

  private Type getTypeForVariable(String variableName) {
    Type type = freeVariablesContext.get(variableName);
    if(type == null) {
      type = specification.getSpecIoVariableByName(variableName).getType();
    }
    return type;
  }

  private List<SExpr> createFreeVariables() {
    return freeVariablesContext.entrySet().stream()
        .filter(item -> !isIoVariable.test(item.getValue()))
        .map(item -> {
      String typeName = item.getValue().getTypeName();
      String variableName = item.getKey();
      return new SList("declare-const", variableName, getSMTLibVariableTypeName(typeName));
    }).collect(Collectors.toList());
  }

  private SExpr createEnumTypes() {

    List<SExpr> definitions = new LinkedList<>();

    specification.getTypeContext().forEach(item -> {
      String typeName = item.getTypeName();
      Optional<List<ValueEnum>> valueEnums = item.match(
          Optional::empty,
          Optional::empty,
          e -> Optional.of(e.getValues())
      );
      if(valueEnums.isPresent()) {
        List<String> arguments = valueEnums.get().stream().map(ValueEnum::getValueString).collect
            (Collectors.toList());
      /*
      (declare-datatypes () ((Color red green blue)))
       */
        definitions.add(new SList(typeName).addListElements(arguments));
      }

    });
    return new SList("declare-datatypes", new SList(), new SList(definitions));
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

  public SConstraint getConstrain() {
    return sConstrain;
  }
}
