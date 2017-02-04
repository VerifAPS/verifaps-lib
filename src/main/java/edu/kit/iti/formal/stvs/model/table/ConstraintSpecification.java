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
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableSet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> implements Commentable {

  private final ObjectProperty<List<SpecProblem>> problems;
  private final ObservableSet<Type> typeContext;
  private final ObservableSet<CodeIoVariable> codeIoVariables;
  private final FreeVariableSet freeVariableSet;
  private final StringProperty comment;
  private final Map<ConstraintCell, CellChangeListener> registeredCellListeners;
  private final NullableProperty<ValidSpecification> validSpecification;

  public ConstraintSpecification(ObservableSet<Type> typeContext,
                                 ObservableSet<CodeIoVariable> ioVariables,
                                 FreeVariableSet freeVariableSet) {
    super();

    this.typeContext = typeContext;
    this.codeIoVariables = ioVariables;
    this.freeVariableSet = freeVariableSet;

    this.problems = new SimpleObjectProperty<>(new ArrayList<>());

    this.comment = new SimpleStringProperty("");

    this.validSpecification = new NullableProperty<>();

    this.registeredCellListeners = new HashMap<>();
  }

  public ObservableSet<Type> getTypeContext() {
    return typeContext;
  }

  public FreeVariableSet getFreeVariableSet() {
    return freeVariableSet;
  }

  public ObservableSet<CodeIoVariable> getCodeIoVariables() {
    return codeIoVariables;
  }

  public NullableProperty<ValidSpecification> validSpecificationProperty() {
    return validSpecification;
  }

  public ValidSpecification getValidSpecification() {
    return validSpecification.get();
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

  private void onSpecificationChanged() {
    ValidSpecification spec = new ValidSpecification(
        new ArrayList<>(),
        new ArrayList<>(),
        typeContext,
        freeVariableSet);

    List<SpecProblem> specProblems = new ArrayList<>();

    boolean specValid = true;

    for (SpecificationColumn<ConstraintCell> column : columns) {
      List<Expression> expressionsForColumn = new ArrayList<>();

      // Check cells for problems
      for (int row = 0; row < column.getCells().size(); row++) {
        try {
          expressionsForColumn.add(expressionOrProblemForCell(
              column.getSpecIoVariable().getName(),
              row,
              column.getCells().get(row)));
        } catch (CellProblem problem) {
          specProblems.add(problem);
          expressionsForColumn.add(null);
          specValid = false;
        }
      }

      SpecIoVariable ioVariable = column.getSpecIoVariable();

      // Check column header for problem
      InvalidIoVarProblem.checkForProblem(ioVariable, codeIoVariables)
          .ifPresent(specProblems::add);

      SpecificationColumn<Expression> validColumn =
          new SpecificationColumn<>(ioVariable, expressionsForColumn, column.getConfig());

      spec.getColumns().add(validColumn);
    }

    for (int row = 0; row < durations.size(); row++) {
      try {
        spec.getDurations().add(lowerBoundedIntervalOrProblemForDuration(
            row,
            durations.get(row)));
      } catch (DurationProblem problem) {
        specProblems.add(problem);
        specValid = false;
      }
    }

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
    ExpressionParser parser = new ExpressionParser(columnId, typeContext);
    Expression expression = parser.parseExpression(cell.getAsString());

    HashMap<String, Type> allTypes = new HashMap<>();
    allTypes.putAll(freeVariableSet.getVariableContext());
    // Use SpecIoVariable for type checking cells, not CodeIoVariable
    // that way, it's possible for the user to write his/her spec without
    // having written code (and getting sensible type errors)
    columns.forEach(column -> allTypes.put(
        column.getSpecIoVariable().getName(),
        column.getSpecIoVariable().getType()));
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
  protected void onColumnAdded(List<? extends SpecificationColumn<ConstraintCell>> added) {
    super.onColumnAdded(added);

    for (SpecificationColumn<ConstraintCell> column : added) {
      column.getCells().forEach(this::subscribeCell);
    }
  }

  @Override
  protected void onColumnRemoved(List<? extends SpecificationColumn<ConstraintCell>> removed) {
    super.onColumnRemoved(removed);

    for (SpecificationColumn<ConstraintCell> column : removed) {
      column.getCells().forEach(this::unsubscribeCell);
    }
    onSpecificationChanged();
  }

  @Override
  protected void onRowAdded(List<? extends SpecificationRow<ConstraintCell>> added) {
    super.onRowAdded(added);

    for (SpecificationRow<ConstraintCell> row : added) {
      row.getCells().values().forEach(this::subscribeCell);
    }
    onSpecificationChanged();
  }

  @Override
  protected void onRowRemoved(List<? extends SpecificationRow<ConstraintCell>> removed) {
    super.onRowRemoved(removed);
    for (SpecificationRow<ConstraintCell> row : removed) {
      for (ConstraintCell cell : row.getCells().values()) {
        unsubscribeCell(cell);
      }
    }
    onSpecificationChanged();
  }

  private void subscribeCell(ConstraintCell cell) {
    CellChangeListener listener = new CellChangeListener();
    cell.stringRepresentationProperty().addListener(listener);
    registeredCellListeners.put(cell, listener);
  }

  private void unsubscribeCell(ConstraintCell cell) {
    CellChangeListener listener = registeredCellListeners.remove(cell);
    cell.stringRepresentationProperty().removeListener(listener);
  }

  private class CellChangeListener implements ChangeListener<String> {
    @Override
    public void changed(ObservableValue<? extends String> obs, String old, String newV) {
      ConstraintSpecification.this.onSpecificationChanged();
    }
  }
}
