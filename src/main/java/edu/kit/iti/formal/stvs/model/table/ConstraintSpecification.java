package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import javafx.beans.property.ListProperty;
import javafx.beans.property.SimpleListProperty;
import javafx.collections.ObservableList;

import java.util.*;
import java.util.function.Consumer;

import static java.util.Optional.empty;

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
    this.typeContext = typeContext;
    this.freeVariableSet = freeVariableSet;
    this.codeIoVariables = ioVariables;
    this.freeVariableSet = freeVariableSet;
    this.problems = new SimpleListProperty<>();
    this.validSpecification = Optional.empty();
    this.columnConfigMap = new HashMap<>();
  }

  public void addEmptyColumn(SpecIoVariable variable) {

  }

  public SpecIoVariable getSpecIoVariableForColumn(String column) {
    return null;
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
   * @return a parsed and type-checked specification
   */
  public Optional<ValidSpecification> getValidSpecification() {
    return null;
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
}
