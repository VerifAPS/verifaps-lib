package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.ViewUtils;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.logic.specification.smtlib.SmtConcretizer;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.common.ErrorMessageDialog;
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;
import javafx.application.Platform;
import javafx.beans.binding.BooleanBinding;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ObservableValue;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Alert;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;

import java.util.List;

public class SpecificationController implements Controller {

  private final GlobalConfig globalConfig;

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
  private SpecificationConcretizer concretizer;

  public SpecificationController(
      ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> codeIoVariables,
      HybridSpecification hybridSpecification,
      ObjectProperty<VerificationState> stateProperty,
      BooleanBinding codeInvalid,
      GlobalConfig globalConfig) {
    this.spec = hybridSpecification;
    this.hybridSpecification = hybridSpecification;
    this.stateProperty = stateProperty;
    this.stateProperty.addListener(new VerificationStateChangeListener());
    this.view = new SpecificationView();
    this.selection = hybridSpecification.getSelection();
    this.globalConfig = globalConfig;
    this.variableCollectionController = new VariableCollectionController(
        typeContext,
        hybridSpecification.getFreeVariableList());
    this.tableController = new SpecificationTableController(
        globalConfig,
        typeContext,
        codeIoVariables,
        variableCollectionController.getValidator().validFreeVariablesProperty(),
        hybridSpecification);
    this.specificationInvalid = new SimpleBooleanProperty(true);
    specificationInvalid.bind(
        variableCollectionController.getValidator().validProperty().not()
            .or(tableController.getValidator().validProperty().not())
            .or(codeInvalid));

    //use event trigger to generate timing-diagram, to minimize code-duplication
    onConcreteInstanceChanged(getConcreteSpecification());

    view.setVariableCollection(variableCollectionController.getView());
    view.setTable(tableController.getView());
    view.getStartButton().setOnAction(new VerificationButtonClickedListener());
    view.getStartButton().disableProperty().bind(specificationInvalid);

    view.getStartConcretizerButton().setOnAction(this::startConretizer);

    hybridSpecification.concreteInstanceProperty().addListener((observable, old, newVal)
        -> this.onConcreteInstanceChanged(newVal));
  }

  private void onConcreteInstanceChanged(ConcreteSpecification newVal) {
    if (getConcreteSpecification() == null) {
      view.setEmptyDiagram(new Label("no timing-diagram available"));
    } else {
      this.timingDiagramCollectionController = new TimingDiagramCollectionController(
          getConcreteSpecification(), selection);
      view.setDiagram(timingDiagramCollectionController.getView());

    }
  }

  private void startConretizer(ActionEvent actionEvent) {
    view.setConcretizerButtonStop();
    view.getStartConcretizerButton().setOnAction(this::stopConcretizer);
    this.concretizer = new SmtConcretizer(globalConfig);
    concretizer.calculateConcreteSpecification(tableController.getValidator().getValidSpecification(),
        variableCollectionController.getValidator().validFreeVariablesProperty().get(),
        optionalSpec -> {
          Platform.runLater(() -> {
            if (optionalSpec.isPresent()) {
              hybridSpecification.setConcreteInstance(optionalSpec.get());
            } else {
              ViewUtils.showDialog(Alert.AlertType.WARNING, "Concretizer warning",
                  "No concrete instance found",
                  "The Solver could not produce a concrete example with the given table.");
            }
            view.setConcretizerButtonStart();
            view.getStartConcretizerButton().setOnAction(this::startConretizer);
          });
        }, exception -> {
          Platform.runLater(() -> {
            new ErrorMessageDialog(exception, "Concretizing failed", "An Error occurred while "
                + "concretizing the specification");
          });
        });
  }

  private void stopConcretizer(ActionEvent actionEvent) {
    view.setConcretizerButtonStart();
    view.getStartConcretizerButton().setOnAction(this::startConretizer);
    if (this.concretizer != null) {
      this.concretizer.terminate();
    }
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
    switch (newState) {
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
      switch (stateProperty.get()) {
        case RUNNING:
          view.onVerificationButtonClicked(hybridSpecification, VerificationEvent.Type.STOP);
          break;
        default:
          view.onVerificationButtonClicked(hybridSpecification, VerificationEvent.Type.START);
      }
    }
  }

  public HybridSpecification getSpec() {
    return spec;
  }
}
