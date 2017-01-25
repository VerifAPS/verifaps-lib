package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.problems.*;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.util.*;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> implements Commentable {

  private ObjectProperty<List<SpecProblem>> problems;
  private Set<Type> typeContext;
  private Set<CodeIoVariable> codeIoVariables;
  private Set<SpecIoVariable> specIoVariables; // TODO: Do we need this (implicitly stored in columns)?
  private FreeVariableSet freeVariableSet;
  /* Need to store this here, because we don't want ALL SpecificationRows to be commentable, only those
  containing ConstraintCells */
  private List<RowComment> rowComments;
  private StringProperty comment;

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

  /**
   * Constructor with full parameters.
   * @param columns
   * @param durations
   * @param typeContext
   * @param ioVariables
   * @param freeVariableSet
   */
  public ConstraintSpecification(Map<String, SpecificationColumn<ConstraintCell>> columns,
                                 List<ConstraintDuration> durations,
                                 Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet) {
    super(columns, durations);
    for (SpecificationColumn<ConstraintCell> col : columns.values()) {
      col.getSpecIoVariable().categoryProperty().addListener(new SpecificationChangedListener<VariableCategory>());
      col.getSpecIoVariable().nameProperty().addListener(new SpecificationChangedListener<String>());
      col.getSpecIoVariable().typeProperty().addListener(new SpecificationChangedListener<Type>());
      for (int i = 0; i < durations.size(); i++) {
        ConstraintCell cell = col.getCellForRow(i);
        cell.stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
      }
    }
    for (int i = 0; i < durations.size(); i++) {
      SpecificationRow<ConstraintCell, ConstraintDuration> row = getRow(i);
      row.getDuration().stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
      row.getDuration().stringRepresentationProperty().addListener(new DurationChangedListener(i));
    }
    this.typeContext = typeContext;
    this.freeVariableSet = freeVariableSet;
    this.codeIoVariables = ioVariables;
    this.freeVariableSet = freeVariableSet;
    this.problems = new SimpleObjectProperty<List<SpecProblem>>();
    this.validSpecification = new OptionalProperty<>(new SimpleObjectProperty<>());
    onSpecificationChanged();
  }

  public void addEmptyColumn(SpecIoVariable variable) {
      if (specIoVariables.contains(variable)) {
        throw new IllegalArgumentException("Column for " + variable.getName() + " already exists");
      }
      ArrayList<ConstraintCell> emptyCells = new ArrayList<ConstraintCell>();
      for (int i = 0; i < durations.size(); i++) {
        emptyCells.add(new ConstraintCell(""));
      }
      addColumn(variable.getName(), new SpecificationColumn<ConstraintCell>(variable, emptyCells, new ColumnConfig()));
      specIoVariables.add(variable);
  }

  /**
   * TODO: Remove?
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

  public void setFreeVariableSet(FreeVariableSet freeVariableSet) {
    this.freeVariableSet = freeVariableSet;
    onSpecificationChanged();
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

  @Override
  public void addColumn(String columnId, SpecificationColumn<ConstraintCell> column) {
    if (specIoVariables.contains(column.getSpecIoVariable())) {
      throw new IllegalArgumentException("Column for " + column.getSpecIoVariable().getName() + " already exists");
    }
    super.addColumn(columnId, column);
    column.getSpecIoVariable().categoryProperty().addListener(new SpecificationChangedListener<VariableCategory>());
    column.getSpecIoVariable().nameProperty().addListener(new SpecificationChangedListener<String>());
    column.getSpecIoVariable().typeProperty().addListener(new SpecificationChangedListener<Type>());
    for (int i = 0; i < durations.size(); i++) {
      ConstraintCell cell = column.getCellForRow(i);
      cell.stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
      // No need to listen for changes to comments, as they have no effect (annotations would)
    }
    specIoVariables.add(column.getSpecIoVariable());
    onSpecificationChanged();
  }

  public void removeColumn(String columnId) {
    specIoVariables.remove(columns.get(columnId).getSpecIoVariable());
    super.removeColumn(columnId);
    onSpecificationChanged();
  }

  public SpecificationRow<ConstraintCell, ConstraintDuration> getRow(int rowNum) {
    SpecificationRow<ConstraintCell, ConstraintDuration> row = super.getRow(rowNum);
    // Register listener so we can adapt durations here if someone changes them through the row
    //row.getDuration().stringRepresentationProperty().addListener(new DurationChangedListener(rowNum));
    return row;
  }

  public void addRow(int rowNum, SpecificationRow<ConstraintCell, ConstraintDuration> row) {
    super.addRow(rowNum, row);
    for (String varName : columns.keySet()) {
      row.getCellForVariable(varName).stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
    }
    row.getDuration().stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
    row.getDuration().stringRepresentationProperty().addListener(new DurationChangedListener(rowNum));
    onSpecificationChanged();
  }

  public void removeRow(int rowNum) {
    super.removeRow(rowNum);
    onSpecificationChanged();
  }

  /**
   * Called when the specification changed. Try to create a new ValidSpecification (parsed and type-checked) if possible;
   * record all problems encountered in doing so. If parsing and type-checking successful, sets the optional ValidSpecification.
   */
  private void onSpecificationChanged() {
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
          problemsFound.add(new TypeErrorProblem("Type error in column " + columnId + ", row " + rowNum, rawColumn.getSpecIoVariable(), rowNum, e));
        }
      }
      parsedColumns.put(columnId, new SpecificationColumn<>(rawColumn.getSpecIoVariable(), parsedCells, rawColumn.getConfig()));
    }
    // Parse durations
    ArrayList<LowerBoundedInterval> parsedDurations = new ArrayList<>();
    for(int i = 0; i < durations.size(); i++) {
      try {
        parsedDurations.add(IntervalParser.parse(durations.get(i).getAsString()));
      } catch (ParseException e) {
        problemsFound.add(new DurationProblem(e.getParseErrorMessage(), i));
      }
    }
    // Are there invalid IO variables? (Is there a specIoVariable that is not a codeIoVariable?)
    for (SpecIoVariable specIoVariable : specIoVariables) {
      if (!codeIoVariables.contains(new CodeIoVariable(specIoVariable.getCategory(), specIoVariable.getType(), specIoVariable.getName()))) {
        problemsFound.add(new InvalidIoVarProblem(specIoVariable));
      }
    }
    // Create the new ValidSpecification
    setProblems(problemsFound);
    boolean validSpecificationPossible = true;
    for (SpecProblem specProblem : problemsFound) {
      if (specProblem instanceof DurationProblem || specProblem instanceof TypeErrorProblem || specProblem instanceof ParseErrorProblem) {
        validSpecificationPossible = false;
      }
    }
    if (validSpecificationPossible) {
      validSpecification.set(new ValidSpecification(parsedColumns, parsedDurations, typeContext, freeVariableSet));
    } else {
      validSpecification.clear();
    }
  }

  private void onDurationChanged(int rownum, String newValue) {
    //Update the internal list of durations
    durations.set(rownum, new ConstraintDuration(newValue));
  }

  private class SpecificationChangedListener<T> implements ChangeListener<T> {

    @Override
    public void changed(ObservableValue<? extends T> observableValue, T oldValue, T newValue) {
      onSpecificationChanged();
    }
  }

  private class DurationChangedListener implements ChangeListener<String> {

    private int rownum;

    public DurationChangedListener(int rownum) {
      this.rownum = rownum;
    }
    @Override
    public void changed(ObservableValue<? extends String> observableValue, String oldValue, String newValue) {
      onDurationChanged(rownum, newValue);
    }
  }
}
