package edu.kit.iti.formal.stvs.model.common;

import java.util.ArrayList;
import java.util.List;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * A list of free variables.
 * @author Philipp
 */
public class FreeVariableList {

  private final ObservableList<FreeVariable> variables;

  public FreeVariableList() {
    this(new ArrayList<>());
  }

  /**
   * Construct a FreeVariableList from a list of {@link FreeVariable}s.
   * @param variables The list of free variables
   */
  public FreeVariableList(List<FreeVariable> variables) {
    this.variables = FXCollections.observableList(variables, FreeVariable.EXTRACTOR);
  }

  /**
   * Copy constructor for deep copies of a {@link FreeVariableList}.
   *
   * @param freeVariableList the list to copy
   */
  public FreeVariableList(FreeVariableList freeVariableList) {
    List<FreeVariable> clonedVariables = new ArrayList<>();
    for (FreeVariable freeVar : freeVariableList.getVariables()) {
      clonedVariables.add(new FreeVariable(freeVar));
    }
    this.variables = FXCollections.observableList(clonedVariables, FreeVariable.EXTRACTOR);
  }

  /**
   * Get the {@link ObservableList} of free variables. This list is "deeply observable", meaning
   * that changes to the properties of the {@link FreeVariable}s it contains cause change events
   * on the list.
   * @return The {@link ObservableList} of {@link FreeVariable}s
   */
  public ObservableList<FreeVariable> getVariables() {
    return variables;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    FreeVariableList that = (FreeVariableList) obj;

    return getVariables() != null ? getVariables().equals(that.getVariables())
        : that.getVariables() == null;
  }

  @Override
  public int hashCode() {
    return getVariables() != null ? getVariables().hashCode() : 0;
  }
}
