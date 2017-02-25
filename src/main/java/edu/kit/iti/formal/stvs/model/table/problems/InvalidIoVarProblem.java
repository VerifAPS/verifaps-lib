package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;
import org.omg.CORBA.DynAnyPackage.Invalid;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class InvalidIoVarProblem extends ColumnProblem {

  public static ValidIoVariable tryGetValidIoVariable(
      SpecIoVariable specIoVariable,
      Collection<CodeIoVariable> codeIoVariables,
      Map<String, Type> typesByName,
      MinorProblemsHandler minorProblemsHandler)
      throws InvalidIoVarProblem {

    String name = tryGetValidName(specIoVariable, codeIoVariables, minorProblemsHandler);
    Type type = tryGetValidType(specIoVariable, typesByName, codeIoVariables, minorProblemsHandler);

    return new ValidIoVariable(specIoVariable.getCategory(), name, type);
  }

  private static Type tryGetValidType(
      SpecIoVariable specIoVariable,
      Map<String, Type> typesByName,
      Collection<CodeIoVariable> codeIoVariables,
      MinorProblemsHandler minorProblemsHandler)
      throws InvalidIoVarProblem {
    Type type = typesByName.get(specIoVariable.getType());
    if (type == null) {
      throw new InvalidIoVarProblem(specIoVariable, ErrorType.TYPE_UNKNOWN);
    }
    codeIoVariables.stream()
        .filter(codeIoVariable -> codeIoVariable.getName().equals(specIoVariable.getName()))
        .findAny().ifPresent(codeIoVariable -> {
      if (!codeIoVariable.getType().equals(specIoVariable.getType())) {
        minorProblemsHandler.handle(
            new InvalidIoVarProblem(specIoVariable, ErrorType.TYPE_MISMATCH));
      }
    });
    return type;
  }

  private static String tryGetValidName(
      SpecIoVariable ioVar,
      Collection<CodeIoVariable> codeIoVariables,
      MinorProblemsHandler minorProblemsHandler)
      throws InvalidIoVarProblem {
    if (!VariableExpr.IDENTIFIER_PATTERN.matcher(ioVar.getName()).matches()) {
      throw new InvalidIoVarProblem(ioVar, ErrorType.NAME_INVALID);
    }
    if (!codeIoVariables.stream().anyMatch(codeIoVar -> codeIoVar.getName().equals(ioVar.getName()))) {
      minorProblemsHandler.handle(
          new InvalidIoVarProblem(ioVar, ErrorType.NAME_MISMATCH));
    }
    return ioVar.getName();
  }

  private static String createMessageForType(ErrorType errorType) {
    switch (errorType) {
      case NAME_MISMATCH: return "Column name in table doesn't match any column name in code";
      case TYPE_MISMATCH: return "Column type in table doesn't match column type in code";
      case CATEGORY_MISMATCH: return "Column category in table doesn't match column category in code";
      case NAME_INVALID: return "Column name is not a valid identifier";
      case TYPE_UNKNOWN: return "Column type is not defined";
      default:
        System.err.println("Unhandled error message errorType in InvalidIoVariableProblem: " + errorType);
        return "Column definition invalid";
    }
  }

  public enum ErrorType {
    NAME_INVALID,
    TYPE_UNKNOWN,

    NAME_MISMATCH,
    TYPE_MISMATCH,
    CATEGORY_MISMATCH
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
