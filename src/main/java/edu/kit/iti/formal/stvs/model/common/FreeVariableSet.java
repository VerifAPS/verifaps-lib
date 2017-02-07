package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import org.apache.commons.lang3.builder.EqualsBuilder;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
/*
  TODO: Possible rename of the class?
  The order in which the elements are placed matters in the gui.
  Therefore, I kept the Lists that were used in the interface definition.
  So there are two possibilities:
  1: Rename the class
  2: Save the order somewhere else (e.g. gui)
*/

/**
 * Created by csicar on 10.01.17.
 */
public class FreeVariableSet {
  private ObservableList<FreeVariable> variableSet = FXCollections.observableArrayList(p ->
      new Observable[]{p.nameProperty(), p.defaultValueProperty(), p.typeProperty()}
  );
  private ObjectProperty<Map<String, Set<FreeVariable>>> problems =
      new SimpleObjectProperty<>(new HashMap<>());

  /**
   * Creates a new list of free variables with an existing base.
   *
   * @param variableList List of existing variables
   */
  public FreeVariableSet(List<FreeVariable> variableList) {
    initItemChangeListener();
    this.variableSet.addAll(variableList);
  }

  /**
   * Creates listener that observes changes to the list to create problems if they exist.
   */
  private void initItemChangeListener() {
    this.variableSet.addListener((ListChangeListener.Change<? extends FreeVariable> change) -> {
      boolean criticalOperationOccurred = false;
      while (change.next()) {
        if (!change.wasPermutated()) {
          criticalOperationOccurred = true;
        }
      }
      if (criticalOperationOccurred) {
        findProblems();
      }
    });
  }

  /**
   * Checks if two or more variables have the same name.
   * If so they are added to the map {@code problems}
   */
  private void findProblems() {
    this.problems.setValue(
        variableSet.stream()
            .map(FreeVariable::getName)
            .distinct()
            .map(this::variablesWithName)
            .filter(set -> set.size() > 1)
            .collect(Collectors.toMap(
                (Set<FreeVariable> set) -> set.iterator().next().getName(), Function.identity()))
    );
  }

  /**
   * Finds variables with the same name
   *
   * @param name Name to be searched
   * @return Set of variables with that name
   */
  private Set<FreeVariable> variablesWithName(String name) {
    return variableSet.stream()
        .filter((FreeVariable var) -> var.getName().equals(name))
        .collect(Collectors.toSet());
  }

  /**
   * Creates a new empty list of free variables.
   */
  public FreeVariableSet() {
    initItemChangeListener();
  }

  /**
   * Creates a map to map from variableNames to the types of their variable.
   *
   * @return Map from Names to Types
   */
  public Map<String, Type> getVariableContext() {
    return variableSet.stream().collect(Collectors
        .toMap(FreeVariable::getName, FreeVariable::getType));
  }

  public ObservableList<FreeVariable> getVariableSet() {
    return variableSet;
  }

  public Map<String, Set<FreeVariable>> getProblems() {
    return problems.get();
  }

  public ObjectProperty<Map<String, Set<FreeVariable>>> problemsProperty() {
    return problems;
  }

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof FreeVariableSet))
      return false;
    if (obj == this)
      return true;

    FreeVariableSet rhs = (FreeVariableSet) obj;
    return new EqualsBuilder().
            append(variableSet, rhs.variableSet).
            append(problems.get(), rhs.problems.get()).
            isEquals();
  }
}
