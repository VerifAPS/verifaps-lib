package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

/**
 * @author Benjamin Alt
 */
public class InvalidIoVarProblem extends ColumnProblem {

  public static Optional<InvalidIoVarProblem> checkForProblem(
      SpecIoVariable specIoVariable, Collection<CodeIoVariable> codeIoVariables) {

    Optional<CodeIoVariable> codeIoVariableOptional = codeIoVariables.stream()
        .filter(ioVar -> ioVar.getName().equals(specIoVariable.getName()))
        .findFirst();
    if (!codeIoVariableOptional.isPresent()) {
      return Optional.of(new InvalidIoVarProblem(specIoVariable, Type.INVALID_NAME));
    }
    CodeIoVariable codeIoVariable = codeIoVariableOptional.get();

    if (specIoVariable.matches(codeIoVariable)) {
      return Optional.empty();
    } else {
      return Optional.of(new InvalidIoVarProblem(specIoVariable, Type.INVALID_TYPE));
    }
  }

  private static String createMessageForType(Type errorType) {
    return "Column " + errorType.getDescription() + " in Table doesn't "
          + "match column name in Code";
  }

  public enum Type {
    INVALID_NAME("name"),
    INVALID_TYPE("type");

    private final String description;

    Type(String description) {
      this.description = description;
    }

    public String getDescription() {
      return description;
    }
  }

  private final SpecIoVariable specIoVariable;
  private final Type type;

  private InvalidIoVarProblem(SpecIoVariable specIoVariable, Type errorType) {
    super(createMessageForType(errorType), specIoVariable.getName());
    this.specIoVariable = specIoVariable;
    this.type = errorType;
  }

  public SpecIoVariable getSpecIoVariable() {
    return specIoVariable;
  }

  public Type getType() {
    return type;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    InvalidIoVarProblem that = (InvalidIoVarProblem) o;

    if (getSpecIoVariable() != null ? !getSpecIoVariable().equals(that.getSpecIoVariable()) : that.getSpecIoVariable() != null)
      return false;
    return getType() == that.getType();
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (getSpecIoVariable() != null ? getSpecIoVariable().hashCode() : 0);
    result = 31 * result + (getType() != null ? getType().hashCode() : 0);
    return result;
  }
}
