package edu.kit.iti.formal.stvs.model.common;

import java.util.ArrayList;
import java.util.List;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * Created by philipp on 09.02.17.
 *
 * @author Philipp
 */
public class FreeVariableList {

  private final ObservableList<FreeVariable> variables;

  public FreeVariableList() {
    this(new ArrayList<>());
  }

  public FreeVariableList(List<FreeVariable> variables) {
    this.variables = FXCollections.observableList(variables, FreeVariable.EXTRACTOR);
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

  public ObservableList<FreeVariable> getVariables() {
    return variables;
  }
}
