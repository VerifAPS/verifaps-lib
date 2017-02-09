package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class InvalidIoVarProblem extends ColumnProblem {

  public static ValidIoVariable tryGetValidIoVariable(
      SpecIoVariable specIoVariable,
      Collection<CodeIoVariable> codeIoVariables,
      Map<String, Type> typesByName,
      Consumer<InvalidIoVarProblem> minorProblemsConsumer)
      throws InvalidIoVarProblem {

    Optional<CodeIoVariable> matchedCodeVar = codeIoVariables.stream()
        .filter(ioVar -> ioVar.getName().equals(specIoVariable.getName()))
        .findAny();
    if (!matchedCodeVar.isPresent()) {
      minorProblemsConsumer.accept(new InvalidIoVarProblem(specIoVariable, ErrorType.NAME_MISMATCH));
    } else if (!specIoVariable.matches(matchedCodeVar.get())) {
      minorProblemsConsumer.accept(new InvalidIoVarProblem(specIoVariable, ErrorType.TYPE_MISMATCH));
    }

    if (!VariableExpr.IDENTIFIER_PATTERN.matcher(specIoVariable.getName()).matches()) {
      throw new InvalidIoVarProblem(specIoVariable, ErrorType.NAME_INVALID);
    }
    Type type = Optional.ofNullable(typesByName.get(specIoVariable.getType()))
        .orElseThrow(() -> new InvalidIoVarProblem(specIoVariable, ErrorType.TYPE_UNKNOWN));

    return new ValidIoVariable(specIoVariable.getCategory(), specIoVariable.getName(), type);
  }

  private static String createMessageForType(ErrorType errorType) {
    switch (errorType) {
      case NAME_MISMATCH: return "Column name in table doesn't match column name in code";
      case TYPE_MISMATCH: return "Column errorType in table doesn't match column name in code";
      case NAME_INVALID: return "Column name is not a valid identifier";
      case TYPE_UNKNOWN: return "Column errorType is not defined";
      default:
        System.err.println("Unhandled error message errorType in InvalidIoVariableProblem: " + errorType);
        return "Column definition invalid";
    }
  }

  public enum ErrorType {
    NAME_INVALID,
    TYPE_UNKNOWN,

    NAME_MISMATCH,
    TYPE_MISMATCH
  }

  private final SpecIoVariable specIoVariable;
  private final ErrorType errorType;

  private InvalidIoVarProblem(SpecIoVariable specIoVariable, ErrorType errorType) {
    super(createMessageForType(errorType), specIoVariable.getName());
    this.specIoVariable = specIoVariable;
    this.errorType = errorType;
  }

  public SpecIoVariable getSpecIoVariable() {
    return specIoVariable;
  }

  public ErrorType getErrorType() {
    return errorType;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    InvalidIoVarProblem that = (InvalidIoVarProblem) o;

    if (getSpecIoVariable() != null ? !getSpecIoVariable().equals(that.getSpecIoVariable()) : that.getSpecIoVariable() != null)
      return false;
    return getErrorType() == that.getErrorType();
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (getSpecIoVariable() != null ? getSpecIoVariable().hashCode() : 0);
    result = 31 * result + (getErrorType() != null ? getErrorType().hashCode() : 0);
    return result;
  }
}
