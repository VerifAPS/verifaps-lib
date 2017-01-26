package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException;

import java.util.function.Function;

/**
 * @author Benjamin Alt
 */
public class TypeErrorProblem extends SpecProblem {

  private final SpecIoVariable column;
  private final int row;
  private final TypeCheckException typeCheckException;
  private final String errorMessage;

  public TypeErrorProblem(String errorMessage, SpecIoVariable column, int row, TypeCheckException typeCheckException) {
    this.column = column;
    this.row = row;
    this.typeCheckException = typeCheckException;
    this.errorMessage = errorMessage;
  }

  @Override
  public <R> R match(
      Function<TypeErrorProblem, R> matchTypeError,
      Function<InvalidIoVarProblem, R> matchInvalidIoVar,
      Function<CyclicDependencyProblem, R> matchCyclicDependency,
      Function<ParseErrorProblem, R> matchParseError,
      Function<DurationProblem, R> matchDurationProblem) {
    return matchTypeError.apply(this);
  }

  public TypeCheckException getTypeCheckException() {
    return typeCheckException;
  }

  @Override
  public String getErrorMessage() {
    return errorMessage;
  }

  public SpecIoVariable getIoVariable() {
    return column;
  }

  public int getRow() {
    return row;
  }
}
