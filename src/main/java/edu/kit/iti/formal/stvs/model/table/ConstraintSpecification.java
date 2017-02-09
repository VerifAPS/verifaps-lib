package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.problems.*;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> implements Commentable {

  public static SpecificationRow<ConstraintCell> createRow(
      Map<String, ConstraintCell> wildcardCells) {
    return new SpecificationRow<>(wildcardCells,
        cell -> new Observable[] { cell.stringRepresentationProperty() });
  }

  private final ObjectProperty<List<SpecProblem>> problems;
  private final ObjectProperty<List<Type>> typeContext;
  private final ObjectProperty<List<CodeIoVariable>> codeIoVariables;
  private final FreeVariableSet freeVariableSet;
  private final StringProperty comment;

  private final NullableProperty<ValidSpecification> validSpecification;

  public ConstraintSpecification(ObjectProperty<List<Type>> typeContext,
                                 ObjectProperty<List<CodeIoVariable>> ioVariables,
                                 FreeVariableSet freeVariableSet) {
    super(durationCell -> new Observable[] { durationCell.stringRepresentationProperty() });

    this.typeContext = typeContext;
    this.codeIoVariables = ioVariables;
    this.freeVariableSet = freeVariableSet;

    this.problems = new SimpleObjectProperty<>(new ArrayList<>());

    this.comment = new SimpleStringProperty("");

    this.validSpecification = new NullableProperty<>();

    this.rows.addListener((Observable observable) -> recalculateSpecProblems());
  }

  public ObjectProperty<List<Type>> typeContextProperty() {
    return typeContext;
  }

  public List<Type> getTypeContext() {
    return typeContext.get();
  }

  public FreeVariableSet getFreeVariableSet() {
    return freeVariableSet;
  }

  public List<CodeIoVariable> getCodeIoVariables() {
    return codeIoVariables.get();
  }

  public ObjectProperty<List<CodeIoVariable>> codeIoVariablesProperty() {
    return codeIoVariables;
  }

  public NullableProperty<ValidSpecification> validSpecificationProperty() {
    return validSpecification;
  }

  public ValidSpecification getValidSpecification() {
    return validSpecification.get();
  }

  public ObjectProperty<List<SpecProblem>> problemsProperty() {
    return this.problems;
  }

  public List<SpecProblem> getProblems() {
    return this.problems.get();
  }

  @Override
  public void setComment(String comment) {
    this.comment.set(comment);
  }

  @Override
  public String getComment() {
    return comment.get();
  }

  @Override
  public StringProperty commentProperty() {
    return comment;
  }

  public void recalculateSpecProblems() {
    ValidSpecification spec = new ValidSpecification(typeContext, freeVariableSet);
    spec.getSpecIoVariables().addAll(getSpecIoVariables());

    List<SpecProblem> specProblems = new ArrayList<>();

    boolean specValid = true;

    for (SpecIoVariable specIoVariable : getSpecIoVariables()) {
      // Check column header for problem
      InvalidIoVarProblem.checkForProblem(specIoVariable, codeIoVariables.get())
          .ifPresent(specProblems::add);
    }

    for (int rowIndex = 0; rowIndex < getRows().size(); rowIndex++) {
      SpecificationRow<ConstraintCell> row = getRows().get(rowIndex);

      Map<String, Expression> expressionsForRow = new HashMap<>();

      // Check cells for problems
      for (Map.Entry<String, ConstraintCell> mapEntry : row.getCells().entrySet()) {
        String columnId = mapEntry.getKey();
        ConstraintCell cell = mapEntry.getValue();

        try {
          expressionsForRow.put(columnId, expressionOrProblemForCell(columnId, rowIndex, cell));
        } catch (CellProblem problem) {
          specProblems.add(problem);
          expressionsForRow.put(columnId, null);
          specValid = false;
        }
      }

      spec.getRows().add(SpecificationRow.createUnobservableRow(expressionsForRow));
    }

    for (int durIndex = 0; durIndex < durations.size(); durIndex++) {
      try {
        spec.getDurations().add(
            lowerBoundedIntervalOrProblemForDuration(durIndex, durations.get(durIndex)));
      } catch (DurationProblem problem) {
        specProblems.add(problem);
        specValid = false;
      }
    }

    this.problems.set(specProblems);

    if (specValid) {
      validSpecification.set(spec);
    } else {
      validSpecification.set(null);
    }
  }

  private LowerBoundedInterval lowerBoundedIntervalOrProblemForDuration(int row, ConstraintDuration duration)
      throws DurationProblem {
    try {
      return IntervalParser.parse(duration.getAsString());
    } catch (ParseException parseException) {
      throw new DurationParseProblem(parseException, row);
    }
  }

  private Expression expressionOrProblemForCell(String columnId, int row, ConstraintCell cell)
      throws CellProblem {
    try {
      return createValidExpressionFromCell(columnId, cell);
    } catch (TypeCheckException typeCheckException) {
      throw new CellTypeProblem(typeCheckException, columnId, row);
    } catch (ParseException parseException) {
      throw new CellParseProblem(parseException, columnId, row);
    } catch (UnsupportedExpressionException unsupportedException) {
      throw new CellUnsupportedExpressionProblem(unsupportedException, columnId, row);
    }
  }

  protected Expression createValidExpressionFromCell(String columnId, ConstraintCell cell)
      throws TypeCheckException, ParseException, UnsupportedExpressionException {
    // First try to parse the expression:
    ExpressionParser parser = new ExpressionParser(columnId, getTypeContext());
    Expression expression = parser.parseExpression(cell.getAsString());

    HashMap<String, Type> allTypes = new HashMap<>();
    allTypes.putAll(freeVariableSet.getVariableContext());
    // Use SpecIoVariable for type checking cells, not CodeIoVariable
    // that way, it's possible for the user to write his/her spec without
    // having written code (and getting sensible type errors)
    getSpecIoVariables().forEach(specIoVariable ->
        allTypes.put(specIoVariable.getName(), specIoVariable.getType()));
    TypeChecker typeChecker = new TypeChecker(allTypes);
    Type type = typeChecker.typeCheck(expression);
    if (type.checksAgainst(TypeBool.BOOL)) {
      return expression;
    } else {
      throw new TypeCheckException(expression,
          "The cell expression must evaluate to a boolean, instead it evaluates to: " + type.getTypeName());
    }
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    ConstraintSpecification that = (ConstraintSpecification) o;

    if (problems != null ? !problems.get().equals(that.problems.get()) : that.problems != null) return false;
    if (freeVariableSet != null ? !freeVariableSet.equals(that.freeVariableSet) : that.freeVariableSet != null)
      return false;
    return comment != null ? comment.get().equals(that.comment.get()) : that.comment == null;

  }

  @Override
  public int hashCode() {
    int result = problems != null ? problems.hashCode() : 0;
    result = 31 * result + (freeVariableSet != null ? freeVariableSet.hashCode() : 0);
    result = 31 * result + (comment != null ? comment.hashCode() : 0);
    return result;
  }
}
