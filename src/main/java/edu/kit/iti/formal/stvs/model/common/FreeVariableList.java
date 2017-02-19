package edu.kit.iti.formal.stvs.model.common;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import java.util.List;

/**
 * Created by philipp on 09.02.17.
 * @author Philipp
 */
public class FreeVariableList {

  private final ObservableList<FreeVariable> variables;

  public FreeVariableList(List<FreeVariable> variables) {
    this.variables = FXCollections.observableList(variables, FreeVariable.EXTRACTOR);
  }

  public ObservableList<FreeVariable> getVariables() {
    return variables;
  }
}
