package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Created by csicar on 09.02.17.
 *
 * @author Carsten Csiky
 */
public class SmtEncoder {
  // Map<Row, Max. number of cycles for that row>
  private final List<ValidIoVariable> ioVariables;
  private final ValidSpecification specification;
  private final Map<String, Type> freeVariablesContext;
  private final List<ValidFreeVariable> validFreeVariables;
  private final List<Integer> maxDurations;
  private final List<String> ioVariableTypes;

  private SmtModel constraint;

  /**
   * Creates an encoder for a specification. Each row is unrolled at most maxDuration times. This is
   * a helper constructor if one do not want to specify a maximum duration for each row.
   *
   * @param maxDuration Max duration for all rows
   * @param specification The specification that should be encoded
   * @param validFreeVariables The free variables that are referred to in {@code specification}
   */
  public SmtEncoder(int maxDuration, ValidSpecification specification,
      List<ValidFreeVariable> validFreeVariables) {
    this(generateAllSameList(maxDuration, specification.getRows().size()), specification,
        validFreeVariables);
  }

  /**
   * Creates an encoder for a specification. Each row is unrolled at most the number specified in
   * {@code maxDurations}.
   *
   * @param maxDurations list of maximum durations for each row
   * @param specification specification to encode
   * @param validFreeVariables free variables that appear in the specification
   */
  public SmtEncoder(List<Integer> maxDurations, ValidSpecification specification,
      List<ValidFreeVariable> validFreeVariables) {
    if (maxDurations.size() != specification.getRows().size()) {
      throw new IllegalArgumentException(
          "Size of maxDurations and size of specification rows do not match");
    }
    this.maxDurations = maxDurations;
    this.specification = specification;
    this.ioVariables = specification.getColumnHeaders();
    this.validFreeVariables = validFreeVariables;
    this.freeVariablesContext = validFreeVariables.stream()
        .collect(Collectors.toMap(ValidFreeVariable::getName, ValidFreeVariable::getType));
    this.ioVariableTypes =
        ioVariables.stream().map(ValidIoVariable::getName).collect(Collectors.toList());

    this.constraint = new SmtModel().addHeaderDefinitions(createFreeVariables())
        .addHeaderDefinitions(setFreeVariablesDefaultValues());

    // Step (2): upper und lower Bound von Durations festlegen
    defineDurationBounds();

    // Step (5)
    unrollRowsToConstraints();

    // Step 4 neg. Indizes verbinden
    connectBackwardReferences();
  }

  /**
   * This connects backward references by aggregating all possible backward references relative to
   * the row before they appeared.
   */
  private void connectBackwardReferences() {
    for (ValidIoVariable ioVariable : this.ioVariables) {
      SpecificationColumn<Expression> column =
          this.specification.getColumnByName(ioVariable.getName());
      String variableName = ioVariable.getName();
      // Iterate over Rows
      for (int z = 0; z < column.getCells().size(); z++) {
        Expression expression = column.getCells().get(z);
        // Add n_x to const declaration
        this.constraint.addHeaderDefinitions(new SList("declare-const", "n_" + z, "(_ BitVec 16)"));
        // Iterate over potential backward steps
        for (int i = 1; i <= getMaxDurationSum(z - 1); i++) {
          // Iterate over possible cycles in last row
          for (int k = 0; k <= getMaxDuration(z - 1); k++) {
            // n_(z-1) = k => A_z_i = A_(z-1)_(k-i)
            this.constraint.addGlobalConstrains(new SList("implies",
                new SList("=", "n_" + (z - 1), BitvectorUtils.hexFromInt(k, 4)),
                new SList("=", "|" + variableName + "_" + z + "_" + (-i) + "|",
                    "|" + variableName + "_" + (z - 1) + "_" + (k - i) + "|")));
            // Add backward reference to const declaration
            this.constraint.addHeaderDefinitions(
                new SList("declare-const", "|" + variableName + "_" + (z - 1) + "_" + (k - i) + "|",
                    getSmtLibVariableTypeName(ioVariable.getValidType())));
          }
          // Add backward reference to const declaration
          this.constraint.addHeaderDefinitions(
              new SList("declare-const", "|" + variableName + "_" + z + "_" + (-i) + "|",
                  getSmtLibVariableTypeName(ioVariable.getValidType())));
        }
      }
    }
  }

  /**
   * Unrolls constraints (expressions are converted to constraints for each cell) to their duration
   * specified in {@code maxDurations}.
   */
  private void unrollRowsToConstraints() {
    for (ValidIoVariable ioVariable : this.ioVariables) {
      SpecificationColumn<Expression> column =
          this.specification.getColumnByName(ioVariable.getName());
      for (int z = 0; z < column.getCells().size(); z++) {
        Expression expression = column.getCells().get(z);

        for (int i = 0; i < getMaxDuration(z); i++) {
          SmtConvertExpressionVisitor visitor =
              new SmtConvertExpressionVisitor(this, z, i, ioVariable);
          SExpression expressionConstraint = expression.takeVisitor(visitor);
          // n_z >= i => ExpressionVisitor(z,i,...)
          this.constraint = new SmtModel(visitor.getConstraint().getGlobalConstraints(),
              visitor.getConstraint().getVariableDefinitions()).combine(this.constraint);
          this.constraint.addGlobalConstrains(new SList("implies",
              new SList("bvuge", "n_" + z, BitvectorUtils.hexFromInt(i, 4)), expressionConstraint));
        }
      }
    }
  }

  /**
   * Adds global constraint to limit durations to their bounds. n_z is limited to [x,y] where x is
   * determined by {@link LowerBoundedInterval#getLowerBound()} for each row and y is determined by
   * {@link LowerBoundedInterval#getUpperBound()} or the entry {@code maxDurations} whichever one is
   * less.
   */
  private void defineDurationBounds() {
    for (int z = 0; z < this.specification.getDurations().size(); z++) {
      LowerBoundedInterval interval = this.specification.getDurations().get(z);
      // n_z >= lowerBound_z
      this.constraint.addGlobalConstrains(new SList("bvuge", "n_" + z,
          BitvectorUtils.hexFromInt(interval.getLowerBound(), 4) + ""));
      // n_z <= upperBound_z
      if (interval.getUpperBound().isPresent()) {
        this.constraint.addGlobalConstrains(new SList("bvule", "n_" + z, BitvectorUtils
            .hexFromInt(Math.min(interval.getUpperBound().get(), getMaxDuration(z)), 4)));
      } else {
        this.constraint.addGlobalConstrains(
            new SList("bvule", "n_" + z, BitvectorUtils.hexFromInt(getMaxDuration(z), 4)));
      }
    }
  }

  /**
   * Generates a List with one number repeated multiple times
   *
   * @param number number to be repeated
   * @param times how many times {@code number} should be repeated
   * @return List of number repeated {@code times} times.
   */
  private static List<Integer> generateAllSameList(int number, int times) {
    return IntStream.generate(() -> number).limit(times).boxed().collect(Collectors.toList());
  }

  /**
   * Generates an expression for the solver of the form (= (variable defaultValue)) for a given
   * variable.
   *
   * @param variable variable for which the assertion should be generated
   * @return asserts that the variable is equal to its default value
   */
  private static SList getDefaultValueEquality(ValidFreeVariable variable) {
    Value defaultValue = variable.getDefaultValue();
    return defaultValue.match(
        (integerVal) -> new SList("=", "|" + variable.getName() + "|",
            BitvectorUtils.hexFromInt(integerVal, 4)),
        (boolVal) -> new SList("=", "|" + variable.getName() + "|", boolVal ? "true" : "false"),
        enumVal -> new SList("=", "|" + variable.getName() + "|",
            BitvectorUtils.hexFromInt(enumVal.getType().getValues().indexOf(enumVal), 4)));
  }

  private static SList getDeclarationForVariable(Type type, String variableName) {
    return new SList("declare-const", "|" + variableName + "|", getSmtLibVariableTypeName(type));
  }

  protected static String getSmtLibVariableTypeName(Type type) {
    return type.match(() -> "(_ BitVec 16)", () -> "Bool", e -> "(_ BitVec 16)");
  }

  protected boolean isIoVariable(String name) {
    return ioVariableTypes.contains(name);
  }

  private List<SExpression> setFreeVariablesDefaultValues() {
    return validFreeVariables.stream().filter(variable -> variable.getDefaultValue() != null)
        .map(SmtEncoder::getDefaultValueEquality).map(sexpr -> new SList("assert", sexpr))
        .collect(Collectors.toList());
  }

  protected Type getTypeForVariable(String variableName) {
    Type type = freeVariablesContext.get(variableName);
    if (type == null) {
      try {
        type = specification.getColumnHeaderByName(variableName).getValidType();
      } catch (NoSuchElementException exception) {
        type = null;
      }
    }
    return type;
  }

  private List<SExpression> createFreeVariables() {
    return freeVariablesContext.entrySet().stream().filter(item -> !isIoVariable(item.getKey()))
        .map(item -> getDeclarationForVariable(item.getValue(), item.getKey()))
        .collect(Collectors.toList());
  }

  private int getMaxDurationSum(int z) {
    int sum = 0;
    for (int i = 0; i <= z; i++) {
      sum += getMaxDuration(i);
    }

    return sum;
  }

  private Integer getMaxDuration(int j) {
    if (j < 0) {
      return 0;
    }
    Optional<Integer> interval = specification.getDurations().get(j).getUpperBound();

    if (interval.isPresent()) {
      return Math.min(maxDurations.get(j), interval.get());
    } else {
      return maxDurations.get(j);
    }
  }

  public SmtModel getConstraint() {
    return constraint;
  }
}
