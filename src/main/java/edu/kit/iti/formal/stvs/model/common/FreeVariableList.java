package edu.kit.iti.formal.stvs.model.common;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by philipp on 09.02.17.
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
