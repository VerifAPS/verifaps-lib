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
import javafx.collections.MapChangeListener;
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
  private final NullableProperty<ValidSpecification> validSpecification;

  private final Map<SpecificationRow<ConstraintCell>, RowChangeListener> registeredRowListeners;
  private final DurationsChangeListener registeredDurationsListener;

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

    this.registeredRowListeners = new HashMap<>();

    this.registeredDurationsListener = new DurationsChangeListener();
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

  private void onSpecificationChanged() {
    ValidSpecification spec = new ValidSpecification(typeContext, freeVariableSet);
    spec.getSpecIoVariables().addAll(getSpecIoVariables());

    List<SpecProblem> specProblems = new ArrayList<>();

    boolean specValid = true;

    for (SpecIoVariable specIoVariable : getSpecIoVariables()) {
      // Check column header for problem
      InvalidIoVarProblem.checkForProblem(specIoVariable, codeIoVariables)
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

      spec.getRows().add(new SpecificationRow<>(expressionsForRow));
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
    ExpressionParser parser = new ExpressionParser(columnId, typeContext);
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
  protected void onRowAdded(List<? extends SpecificationRow<ConstraintCell>> added) {
    super.onRowAdded(added);

    for (SpecificationRow<ConstraintCell> row : added) {
      registeredRowListeners.put(row, new RowChangeListener(row));
    }
    onSpecificationChanged();
  }

  @Override
  protected void onRowRemoved(List<? extends SpecificationRow<ConstraintCell>> removed) {
    super.onRowRemoved(removed);
    for (SpecificationRow<ConstraintCell> row : removed) {
      registeredRowListeners.remove(row);
    }
    onSpecificationChanged();
  }

  @Override
  protected void onDurationAdded(List<? extends ConstraintDuration> added) {
    super.onDurationAdded(added);
    added.forEach(registeredDurationsListener::subscribeCell);
    onSpecificationChanged();
  }

  @Override
  protected void onDurationRemoved(List<? extends ConstraintDuration> removed) {
    super.onDurationRemoved(removed);
    removed.forEach(registeredDurationsListener::unsubscribeCell);
    onSpecificationChanged();
  }

  protected int registeredListeners() {
    return registeredRowListeners.values().stream()
        .map(RowChangeListener::registeredListeners)
        .reduce(0, (a, b) -> a + b);
  }

  private class RowChangeListener implements MapChangeListener<String, ConstraintCell> {

    private final Map<ConstraintCell, CellChangeListener> registeredCellListeners = new HashMap<>();

    public RowChangeListener(SpecificationRow<ConstraintCell> row) {
      row.getCells().values().forEach(this::subscribeCell);
    }

    private class CellChangeListener implements ChangeListener<String> {

      @Override
      public void changed(ObservableValue<? extends String> obs, String old, String newV) {
        ConstraintSpecification.this.onSpecificationChanged();
      }
    }

    @Override
    public void onChanged(Change<? extends String, ? extends ConstraintCell> change) {
      if (change.wasAdded()) {
        subscribeCell(change.getValueAdded());
      }
      if (change.wasRemoved()) {
        unsubscribeCell(change.getValueRemoved());
      }
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

    protected int registeredListeners() {
      return registeredRowListeners.size();
    }
  }

  private class DurationsChangeListener {
    private class DurationCellListener implements ChangeListener<String> {
      @Override
      public void changed(ObservableValue<? extends String> observable, String oldValue, String newValue) {
        ConstraintSpecification.this.onSpecificationChanged();
      }
    }

    private final DurationCellListener listener = new DurationCellListener();

    private void subscribeCell(ConstraintDuration constraintDuration) {
      constraintDuration.stringRepresentationProperty().addListener(listener);
    }

    private void unsubscribeCell(ConstraintDuration constraintDuration) {
      constraintDuration.stringRepresentationProperty().removeListener(listener);
    }
  }

}
