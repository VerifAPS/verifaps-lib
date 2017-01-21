package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import javafx.beans.property.ListProperty;
import javafx.beans.property.SimpleListProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableList;

import java.util.*;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> {

  private ListProperty<SpecProblem> problems;
  private Set<Type> typeContext;
  private Set<CodeIoVariable> codeIoVariables;
  private Set<SpecIoVariable> specIoVariables;
  private FreeVariableSet freeVariableSet;
  private List<RowComment> rowComments;
  private Optional<ValidSpecification> validSpecification;
  private Map<String, ColumnConfig> columnConfigMap;

  public ConstraintSpecification(Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet) {
    super();
    this.typeContext = typeContext;
    this.freeVariableSet = freeVariableSet;
    this.codeIoVariables = ioVariables;
    this.freeVariableSet = freeVariableSet;
    this.problems = new SimpleListProperty<>();
    this.validSpecification = Optional.empty();
    this.columnConfigMap = new HashMap<>();
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

  public List<RowComment> getRowComments() {
    return rowComments;
  }

  public void setRowComments(List<RowComment> rowComments) {
    this.rowComments = rowComments;
  }

  /**
   * TODO: When to do the parsing and type checking? Ideally any time a constraintCell/duration/SpecIoVariable changes --> must register listeners for these events
   * @return a parsed and type-checked specification
   */
  public Optional<ValidSpecification> getValidSpecification() {
    return validSpecification;
  }

  @Override
  public void addColumn(String columnId, SpecificationColumn<ConstraintCell> column) {
    super.addColumn(columnId, column);
    column.getSpecIoVariable().typeProperty().addListener(new SpecificationChangedListener<Type>());
    column.getSpecIoVariable().nameProperty().addListener(new SpecificationChangedListener<String>());
    column.getSpecIoVariable().categoryProperty().addListener(new SpecificationChangedListener<VariableCategory>());
  }

  public void removeColumn(String columnId) {
    super.removeColumn(columnId);

  }

  public ObservableList<SpecProblem> getProblems() {
    return problems.get();
  }

  public ListProperty<SpecProblem> problemsProperty() {
    return problems;
  }

  public void setProblems(ObservableList<SpecProblem> problems) {
    this.problems.set(problems);
  }

  private void onSpecificationChanged() {

  }

  class SpecificationChangedListener<T> implements ChangeListener<T> {
    @Override
    public void changed(ObservableValue observableValue, Object o, Object t1) {
      onSpecificationChanged();
    }
  }
}
