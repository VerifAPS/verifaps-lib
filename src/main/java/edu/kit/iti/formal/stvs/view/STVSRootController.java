package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.STVSRootModel;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.collections.ObservableList;

import java.util.Comparator;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSRootController implements Controller {
  private STVSRootView view;
  private STVSRootModel STVSRootModel;
  private ObservableList<Type> types;
  private ObservableList<CodeIoVariable> ioVars;
  /**
   * Used to sort Types (Enums should be at the bottom)
   */
  private Comparator<Type> typeComparator;

  public STVSRootView getView() {
    return view;
  }

  private void onIOVariablesChange(List<CodeIoVariable> ioVars) {

  }

  private void onTypesChange(List<Type> types) {

  }

  private void onMementoApplied() {

  }
}
