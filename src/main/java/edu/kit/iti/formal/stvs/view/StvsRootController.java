package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController;
import edu.kit.iti.formal.stvs.view.spec.SpecificationTabController;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPaneController;
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController;
import javafx.beans.property.ObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import java.util.Comparator;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsRootController implements Controller {
  private final StvsRootView view;
  private final StvsRootModel stvsRootModel;
  private final ObservableList<Type> types;
  private final ObservableList<CodeIoVariable> ioVars;
  private final EditorPaneController editorPaneController;
  private final SpecificationsPaneController specificationsPaneController;
  /**
   * Used to sort Types (Enums should be at the bottom)
   */
  private final Comparator<Type> typeComparator = null; // TODO this should not be null

  public StvsRootController(StvsRootModel rootModel) {
    this.stvsRootModel = rootModel;
    this.editorPaneController = new EditorPaneController(
        stvsRootModel.getScenario().getCode(),
        stvsRootModel.getGlobalConfig()
    );

    // TODO: Maybe make this ObjectProperty<List<Type>> and change on code change
    // maybe even put this into root model or somewhere
    // TODO: Link this to Code.parsedCodeProperty()
    this.types = FXCollections.observableArrayList(TypeInt.INT, TypeBool.BOOL);
    // TODO: Same. Link this too
    this.ioVars = FXCollections.emptyObservableList();
    this.specificationsPaneController = new SpecificationsPaneController(
        stvsRootModel.getHybridSpecifications(),
        stvsRootModel.getScenario().verificationState(),
        stvsRootModel.getGlobalConfig()
    );

    this.view = new StvsRootView(
        editorPaneController.getView(),
        specificationsPaneController.getView());
  }

  public StvsRootView getView() {
    return view;
  }

  private void onIoVariablesChange(List<CodeIoVariable> ioVars) {

  }

  private void onTypesChange(List<Type> types) {

  }

}
