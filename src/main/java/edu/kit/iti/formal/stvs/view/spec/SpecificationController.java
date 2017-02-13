package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;
import javafx.beans.binding.Bindings;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ObservableValue;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.ContextMenu;

import java.util.List;

public class SpecificationController implements Controller {

  private HybridSpecification spec;
  private ObjectProperty<VerificationState> stateProperty;
  private ContextMenu contextMenu;
  private SpecificationView view;
  private VariableCollectionController variableCollectionController;
  private SpecificationTableController tableController;
  private TimingDiagramCollectionController timingDiagramCollectionController;
  private Selection selection;
  private HybridSpecification hybridSpecification;
  private BooleanProperty specificationInvalid;

  public SpecificationController(
      ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> codeIoVariables,
      HybridSpecification hybridSpecification,
      ObjectProperty<VerificationState> stateProperty) {
    this.spec = hybridSpecification;
    this.hybridSpecification = hybridSpecification;
    this.stateProperty = stateProperty;
    this.stateProperty.addListener(new VerificationStateChangeListener());
    this.view = new SpecificationView();
    this.selection = new Selection();
    this.variableCollectionController = new VariableCollectionController(
        typeContext,
        hybridSpecification.getFreeVariableList());
    this.tableController = new SpecificationTableController(
        typeContext,
        codeIoVariables,
        variableCollectionController.getValidator().validFreeVariablesProperty(),
        hybridSpecification);
    this.specificationInvalid = new SimpleBooleanProperty(true);
    specificationInvalid.bind(Bindings.or(
        Bindings.not(variableCollectionController.getValidator().validProperty()),
        Bindings.not(tableController.getValidator().validProperty())));

    if (getConcreteSpecification() != null) {
      this.timingDiagramCollectionController = new TimingDiagramCollectionController
          (getConcreteSpecification(), selection);
      view.setDiagram(timingDiagramCollectionController.getView());
    }

    view.setVariableCollection(variableCollectionController.getView());
    view.setTable(tableController.getView());
    view.getStartButton().setOnAction(new VerificationButtonClickedListener());
    view.getStartButton().disableProperty().bind(specificationInvalid);
  }

  private ConcreteSpecification getConcreteSpecification() {
    return hybridSpecification.getCounterExample().orElse(
        hybridSpecification.getConcreteInstance().orElse(null));
  }

  public SpecificationView getView() {
    return view;
  }

  private class VerificationStateChangeListener implements javafx.beans.value.ChangeListener<VerificationState> {

    @Override
    public void changed(ObservableValue<? extends VerificationState> observableValue,
                        VerificationState oldState, VerificationState newState) {
      onVerificationStateChanged(newState);
    }
  }

  private void onVerificationStateChanged(VerificationState newState) {
    switch(newState) {
      case RUNNING:
        getView().setVerificationButtonStop();
        break;
      default:
        getView().setVerificationButtonPlay();
    }
  }


  private class VerificationButtonClickedListener implements EventHandler<ActionEvent> {
    @Override
    public void handle(ActionEvent actionEvent) {
      switch(stateProperty.get()) {
        case RUNNING:
          view.onVerificationButtonClicked(hybridSpecification, VerificationEvent.Type.STOP);
          break;
        default:
          view.onVerificationButtonClicked(hybridSpecification, VerificationEvent.Type.START);
      }
    }
  }
}