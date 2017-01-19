package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import java.util.List;
import java.util.Map;
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
  private ObservableList<FreeVariable> variableSet = FXCollections.observableArrayList();

  /**
   * Creates a new list of free variables with an existing base.
   *
   * @param variableSet List of existing variables
   */
  public FreeVariableSet(List<FreeVariable> variableSet) {
    this.variableSet.addAll(variableSet);
  }

  /**
   * Creates a new empty list of free variables.
   */
  public FreeVariableSet() {
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
}
