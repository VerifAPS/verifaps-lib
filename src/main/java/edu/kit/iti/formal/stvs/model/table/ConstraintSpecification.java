package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.problems.ParseErrorProblem;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.model.table.problems.TypeErrorProblem;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.util.*;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> {

  private ObjectProperty<List<SpecProblem>> problems;
  private Set<Type> typeContext;
  private Set<CodeIoVariable> codeIoVariables; //TODO: Do we need this?
  private Set<SpecIoVariable> specIoVariables; // TODO: Do we need this (implicitly stored in columns)?
  private FreeVariableSet freeVariableSet;
  private List<RowComment> rowComments;
  private OptionalProperty<ValidSpecification> validSpecification;

  /**
   * TODO: Should we keep this constructor?
   * @param typeContext
   * @param ioVariables
   * @param freeVariableSet
   */
  public ConstraintSpecification(Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet) {
    super();
    this.typeContext = typeContext;
    this.freeVariableSet = freeVariableSet;
    this.codeIoVariables = ioVariables;
    this.freeVariableSet = freeVariableSet;
    this.problems = new SimpleObjectProperty<List<SpecProblem>>();
    this.validSpecification = new OptionalProperty<>(new SimpleObjectProperty<>());
  }

  public ConstraintSpecification(Map<String, SpecificationColumn<ConstraintCell>> columns, List<ConstraintDuration> durations,
                                 Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet) {
    super(columns, durations);
    this.typeContext = typeContext;
    this.freeVariableSet = freeVariableSet;
    this.codeIoVariables = ioVariables;
    this.freeVariableSet = freeVariableSet;
    this.problems = new SimpleObjectProperty<List<SpecProblem>>();
    this.validSpecification = new OptionalProperty<>(new SimpleObjectProperty<>());
  }

  public void addEmptyColumn(SpecIoVariable variable) {
      ArrayList<ConstraintCell> emptyCells = new ArrayList<ConstraintCell>();
      for (int i = 0; i < durations.size(); i++) {
        emptyCells.add(new ConstraintCell(""));
      }
      addColumn(variable.getName(), new SpecificationColumn<ConstraintCell>(variable, emptyCells, new ColumnConfig()));
  }

  /**
   * TODO
   * This method is redundant, as one can just do SpecificationTable.getColumn(column).getSpecIoVariable()
   */
  @Deprecated
  public SpecIoVariable getSpecIoVariableForColumn(String column) {
    throw new UnsupportedOperationException("This method is on the kill list and may be removed at any time. See Javadoc for alternative");
  }

  public Set<Type> getTypeContext() {
    return typeContext;
  }

  public void setTypeContext(Set<Type> typeContext) {
    this.typeContext = typeContext;
  }

  public FreeVariableSet getFreeVariableSet() {
    return freeVariableSet;
  }

  public ValidSpecification getValidSpecification() {
    return validSpecification.get();
  }

  public OptionalProperty<ValidSpecification> validSpecificationProperty() {
    return validSpecification;
  }

  public List<RowComment> getRowComments() {
    return rowComments;
  }

  public void setRowComments(List<RowComment> rowComments) {
    this.rowComments = rowComments;
  }

  public List<SpecProblem> getProblems() {
    return problems.get();
  }

  public ObjectProperty<List<SpecProblem>> problemsProperty() {
    return problems;
  }

  public void setProblems(List<SpecProblem> problems) {
    this.problems.set(problems);
  }


  class SpecificationChangedListener<T> implements ChangeListener<T> {

    @Override
    public void changed(ObservableValue<? extends T> observableValue, T t, T t1) {
      onSpecificationChanged();
    }
  }

  @Override
  public void addColumn(String columnId, SpecificationColumn<ConstraintCell> column) {
    super.addColumn(columnId, column);
    column.getSpecIoVariable().categoryProperty().addListener(new SpecificationChangedListener<VariableCategory>());
    column.getSpecIoVariable().nameProperty().addListener(new SpecificationChangedListener<String>());
    column.getSpecIoVariable().typeProperty().addListener(new SpecificationChangedListener<Type>());
    for (int i = 0; i < durations.size(); i++) {
      ConstraintCell cell = column.getCellForRow(i);
      cell.stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
      // No need to listen for changes to comments, as they have no effect (annotations would)
    }
  }

  public void removeColumn(String columnId) {
    super.removeColumn(columnId);
    onSpecificationChanged();
  }

  public void addRow(int rowNum, SpecificationRow<ConstraintCell, ConstraintDuration> row) {
    super.addRow(rowNum, row);
    for (String varName : columns.keySet()) {
      row.getCellForVariable(varName).stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
    }
    row.getDuration().stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
  }

  public void removeRow(int rowNum) {
    super.removeRow(rowNum);
    onSpecificationChanged();
  }

  /**
   * Called when the specification changed. Try to create a new ValidSpecification (parsed and type-checked) if possible;
   * record all problems encountered in doing so. If parsing and type-checking successful, sets the optional ValidSpecification.
   */
  void onSpecificationChanged() {
    ArrayList<SpecProblem> problemsFound = new ArrayList<>();
    // Parse and type-check cells
    HashMap<String,SpecificationColumn<Expression>> parsedColumns = new HashMap<>();
    HashMap<String, Type> typeCheckerTypeContext = new HashMap<>(freeVariableSet.getVariableContext());
    for (String columnId : columns.keySet()) {
      typeCheckerTypeContext.put(columnId, columns.get(columnId).getSpecIoVariable().getType());
    }
    TypeChecker typeChecker = new TypeChecker(typeCheckerTypeContext);
    for (String columnId : columns.keySet()) {
      SpecificationColumn<ConstraintCell> rawColumn = columns.get(columnId);
      ArrayList<Expression> parsedCells = new ArrayList<Expression>();
      List<ConstraintCell> rawCells = rawColumn.getCells();
      ExpressionParser parser = new ExpressionParser(columnId);
      for (int rowNum = 0; rowNum < rawCells.size(); rowNum++) {
        try {
          Expression parsedExpression = parser.parseExpression(rawCells.get(rowNum).getAsString());
          parsedCells.add(parsedExpression);
          typeChecker.typeCheck(parsedExpression);
        } catch (ParseException | UnsupportedExpressionException e) {
          problemsFound.add(new ParseErrorProblem(e.getMessage(), rawColumn.getSpecIoVariable(), rowNum));
          // Do not break, as all cells must be parsed in order for all specProblems to be found
        } catch (TypeCheckException e) {
          problemsFound.add(new TypeErrorProblem(rawColumn.getSpecIoVariable(), rowNum, e));
        }
      }
      parsedColumns.put(columnId, new SpecificationColumn<>(rawColumn.getSpecIoVariable(), parsedCells, rawColumn.getConfig()));
    }
    // TODO: Parse and type-check durations
    // For debugging, make all durations "1"
    ArrayList<LowerBoundedInterval> parsedDurations = new ArrayList<>();
    for(int i = 0; i < durations.size(); i++) {
      parsedDurations.add(new LowerBoundedInterval(1, Optional.of(1)));
    }
    // Create the new ValidSpecification
    setProblems(problemsFound);
    if (problemsFound.size() == 0) {
      validSpecification.set(new ValidSpecification(parsedColumns, parsedDurations, typeContext, freeVariableSet));
    } else {
      validSpecification.clear();
    }
  }
}
