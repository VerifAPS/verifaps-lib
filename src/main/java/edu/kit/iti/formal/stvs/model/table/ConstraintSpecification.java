package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.problems.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableSet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> implements Commentable {

  private ObjectProperty<List<SpecProblem>> problems;
  private ObservableSet<Type> typeContext;
  private ObservableSet<CodeIoVariable> codeIoVariables;
  private final FreeVariableSet freeVariableSet;
  private StringProperty comment;

  private OptionalProperty<ValidSpecification> validSpecification;

  /**
   * @param typeContext
   * @param ioVariables
   * @param freeVariableSet
   */
  public ConstraintSpecification(Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet) {
    this(new ArrayList<>(), new ArrayList<>(), typeContext, ioVariables, freeVariableSet);
  }

  /**
   * Constructor with full parameters.
   * @param columns
   * @param durations
   * @param typeContext
   * @param ioVariables
   * @param freeVariableSet
   */
  public ConstraintSpecification(List<SpecificationColumn<ConstraintCell>> columns,
                                 List<ConstraintDuration> durations,
                                 Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet) {
    this.columns = FXCollections.observableArrayList(
        (SpecificationColumn<ConstraintCell> column) -> new Observable[]{column.getSpecIoVariable
            ().categoryProperty(), column.getSpecIoVariable().typeProperty(), column
            .getSpecIoVariable().nameProperty(), column.getCells()});
    this.columns.addAll(columns);
    this.columns.addListener(new ColumnsChangedListener());
    this.columns.addListener(new SpecificationChangedListListener<>());
    initHeight();
    this.rows = FXCollections.observableArrayList(makeRowList(columns));
    this.rows.addListener(new RowsChangedListener());

    this.durations = FXCollections.observableArrayList(
        (ConstraintDuration tp) -> new Observable[]{tp.stringRepresentationProperty()});
    this.durations.addAll(durations);
    this.durations.addListener(new SpecificationChangedListListener<>());
    this.typeContext = FXCollections.observableSet(typeContext);
    this.freeVariableSet = freeVariableSet;
    this.codeIoVariables = FXCollections.observableSet(ioVariables);
    this.problems = new SimpleObjectProperty<>();
    this.validSpecification = new OptionalProperty<>(new SimpleObjectProperty<>());
    onSpecificationChanged();
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

  public ValidSpecification getValidSpecification() {
    return validSpecification.get();
  }

  public OptionalProperty<ValidSpecification> validSpecificationProperty() {
    return validSpecification;
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

  /**
   * Called when the specification changed. Try to create a new ValidSpecification (parsed and type-checked) if possible;
   * record all problems encountered in doing so. If parsing and type-checking successful, sets the optional ValidSpecification.
   */
  private void onSpecificationChanged() {
    ArrayList<SpecProblem> problemsFound = new ArrayList<>();
    // Parse and type-check cells
    HashMap<String,SpecificationColumn<Expression>> parsedColumns = new HashMap<>();
    HashMap<String, Type> typeCheckerTypeContext = new HashMap<>(freeVariableSet.getVariableContext());
    for (SpecificationColumn column : columns) {
      typeCheckerTypeContext.put(column.getSpecIoVariable().getName(), column.getSpecIoVariable().getType());
    }
    TypeChecker typeChecker = new TypeChecker(typeCheckerTypeContext);
    for (SpecificationColumn column : columns) {
      SpecificationColumn<ConstraintCell> rawColumn = column;
      String columnId = column.getSpecIoVariable().getName();
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
          problemsFound.add(new TypeErrorProblem("Type error in column " + columnId + ", row " +
              rowNum, rawColumn.getSpecIoVariable(), rowNum, e));
        }
      }
      parsedColumns.put(columnId, new SpecificationColumn<>(rawColumn.getSpecIoVariable(), parsedCells, rawColumn.getConfig()));
    }
    // Parse durations
    List<LowerBoundedInterval> parsedDurations = new ArrayList<>();
    for(int rownum = 0; rownum < durations.size(); rownum++) {
      try {
        parsedDurations.add(IntervalParser.parse(durations.get(rownum).getAsString()));
      } catch (ParseException e) {
        problemsFound.add(new DurationProblem(e.getParseErrorMessage(), rownum));
      }
    }
    // Are there invalid IO variables? (Is there a specIoVariable that is not a codeIoVariable?)
    for (SpecificationColumn column : columns) {
      boolean found = false;
      for (CodeIoVariable codeIoVariable : codeIoVariables) {
        if (codeIoVariable.matches(column.getSpecIoVariable())) {
          found = true;
        }
      }
      if (!found) {
        problemsFound.add(new InvalidIoVarProblem(column.getSpecIoVariable()));
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

  private class SpecificationChangedListener<T> implements ChangeListener<T> {

    @Override
    public void changed(ObservableValue<? extends T> observableValue, T oldValue, T newValue) {
      onSpecificationChanged();
    }
  }

  private class SpecificationChangedListListener<T> implements ListChangeListener<T> {

    @Override
    public void onChanged(Change<? extends T> change) {
      onSpecificationChanged();
    }
  }

}
