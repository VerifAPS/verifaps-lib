package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollection;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;
import javafx.beans.property.ObjectProperty;
import javafx.scene.control.ContextMenu;

import java.util.List;

public class SpecificationController implements Controller {

  private HybridSpecification spec;
  private ObjectProperty<VerificationState> stateProperty;
  private ContextMenu contextMenu;
  private SpecificationView view;
  private VariableCollectionController variableCollectionController;
  private TimingDiagramCollectionController timingDiagramCollectionController;

  public SpecificationController(
      HybridSpecification hybridSpecification,
      ObjectProperty<List<Type>> codeTypes,
      ObjectProperty<VerificationState> stateProperty) {
    this.spec = hybridSpecification;
    this.stateProperty = stateProperty;
    this.view = new SpecificationView();
    this.variableCollectionController = new VariableCollectionController(codeTypes,
        hybridSpecification.getFreeVariableSet());
  }

  public SpecificationView getView() {
    return view;
  }


}