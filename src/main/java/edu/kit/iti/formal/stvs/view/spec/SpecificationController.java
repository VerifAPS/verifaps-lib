package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;
import javafx.beans.property.ObjectProperty;
import javafx.scene.control.ContextMenu;

import java.io.File;
import java.io.FileInputStream;

public class SpecificationController implements Controller {

  private HybridSpecification spec;
  private ObjectProperty<VerificationState> stateProperty;
  private ContextMenu contextMenu;
  private SpecificationView view;
  private VariableCollectionController variableCollectionController;
  private SpecificationTableController tableController;
  private TimingDiagramCollectionController timingDiagramCollectionController;
  private Selection selection;
  private  HybridSpecification hybridSpecification;

  public SpecificationController(
      HybridSpecification hybridSpecification,
      ObjectProperty<VerificationState> stateProperty) {
    this.spec = hybridSpecification;
    this.hybridSpecification = hybridSpecification;
    this.stateProperty = stateProperty;
    this.view = new SpecificationView();
    this.selection = new Selection();
    this.variableCollectionController = new VariableCollectionController(
        hybridSpecification.typeContextProperty(),
        hybridSpecification.getFreeVariableSet());
    this.tableController = new SpecificationTableController(
        hybridSpecification.typeContextProperty(),
        hybridSpecification.codeIoVariablesProperty(),
        hybridSpecification.getFreeVariableSet()); //TODO: Use actual hybridSpecification and take its content

    if (getConcreteSpecification() != null) {
      this.timingDiagramCollectionController = new TimingDiagramCollectionController
          (getConcreteSpecification(), selection);
      view.setDiagram(timingDiagramCollectionController.getView());
    }
    view.setVariableCollection(variableCollectionController.getView());
    view.setTable(tableController.getView());
  }

  private ConcreteSpecification getConcreteSpecification() {
    return hybridSpecification.getConcreteInstance() == null ? hybridSpecification
        .getConcreteInstance() : hybridSpecification.getConcreteInstance();
  }

  public SpecificationView getView() {
    return view;
  }

}