package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.logic.specification.smtlib.SmtConcretizer;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.util.AsyncRunner;
import edu.kit.iti.formal.stvs.util.AsyncTaskCompletedHandler;
import edu.kit.iti.formal.stvs.util.JavaFxAsyncProcessTask;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;

import java.util.List;

import javafx.beans.binding.BooleanBinding;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.ListChangeListener;
import javafx.event.ActionEvent;
import javafx.scene.control.Alert;
import javafx.scene.control.MenuItem;

/**
 * This is the controller for the {@link SpecificationView}. It handles most of the view logic that
 * is invoked by verification/concretizer results.
 *
 * @author Carsten Csiky
 */
public class SpecificationController implements Controller {

  private final GlobalConfig globalConfig;
  private final ConcretizationTaskHandler concretizationHandler;
  private HybridSpecification spec;
  private ObjectProperty<VerificationState> stateProperty;
  private SpecificationView view;
  private VariableCollectionController variableCollectionController;
  private SpecificationTableController tableController;
  private TimingDiagramCollectionController timingDiagramCollectionController;
  private Selection selection;
  private HybridSpecification hybridSpecification;
  private BooleanProperty specificationInvalid;
  private BooleanProperty specificationConcretizable;
  private JavaFxAsyncProcessTask<ConcreteSpecification> concretizingTask;

  /**
   * This creates an instance of the controller.
   *
   * @param typeContext available types in code
   * @param codeIoVariables available variables in code
   * @param hybridSpecification specification that should be represented by this controller
   * @param stateProperty the state of the verification
   * @param codeInvalid Tells if the code is valid
   * @param globalConfig Global config object
   */
  public SpecificationController(ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> codeIoVariables, HybridSpecification hybridSpecification,
      ObjectProperty<VerificationState> stateProperty, BooleanBinding codeInvalid,
      GlobalConfig globalConfig) {
    this.spec = hybridSpecification;
    this.hybridSpecification = hybridSpecification;
    this.stateProperty = stateProperty;
    this.stateProperty.addListener(this::onVerificationStateChanged);
    this.view = new SpecificationView();
    this.selection = hybridSpecification.getSelection();
    this.globalConfig = globalConfig;
    this.variableCollectionController =
        new VariableCollectionController(typeContext, hybridSpecification.getFreeVariableList());
    this.tableController = new SpecificationTableController(globalConfig, typeContext,
        codeIoVariables, variableCollectionController.getValidator().validFreeVariablesProperty(),
        hybridSpecification);
    this.specificationInvalid = new SimpleBooleanProperty(true);
    specificationInvalid.bind(variableCollectionController.getValidator().validProperty().not()
        .or(tableController.getValidator().validProperty().not()).or(codeInvalid));
    this.specificationConcretizable = new SimpleBooleanProperty(true);
    specificationConcretizable
        .bind(tableController.getValidator().validSpecificationProperty().isNotNull());
    this.concretizationHandler = new ConcretizationTaskHandler();

    // use event trigger to generate timing-diagram, to minimize code-duplication
    onConcreteInstanceChanged(getConcreteSpecification());

    view.setVariableCollection(variableCollectionController.getView());
    view.getVariableCollection().getFreeVariableTableView()
        .setEditable(this.hybridSpecification.isEditable());
    List<MenuItem> freeVarMenuItems =
        view.getVariableCollection().getFreeVariableTableView().getContextMenu().getItems();
    for (MenuItem menuItem : freeVarMenuItems) {
      menuItem.setDisable(!this.hybridSpecification.isEditable());
    }
    view.setTable(tableController.getView());
    view.getStartButton().setOnAction(this::onVerificationButtonClicked);
    view.getStartButton().disableProperty().bind(specificationInvalid);
    view.getStartConcretizerButton().disableProperty().bind(specificationConcretizable.not());

    view.getStartConcretizerButton().setOnAction(this::startConcretizer);

    hybridSpecification.concreteInstanceProperty()
        .addListener((observable, old, newVal) -> this.onConcreteInstanceChanged(newVal));
    registerTimingDiagramDeactivationHandler();
  }

  private void onVerificationStateChanged(
      ObservableValue<? extends VerificationState> observableValue, VerificationState oldState,
      VerificationState newState) {
    switch (newState) {
      case RUNNING:
        getView().setVerificationButtonStop();
        break;
      default:
        getView().setVerificationButtonPlay();
    }
  }

  private void registerTimingDiagramDeactivationHandler() {
    hybridSpecification.getDurations().addListener(this::specChanged);
    hybridSpecification.getColumnHeaders().addListener(this::specChanged);
    hybridSpecification.getRows().addListener(this::specChanged);
    hybridSpecification.getFreeVariableList().getVariables().addListener(this::specChanged);
    hybridSpecification.setConcreteInstance(null);
  }

  private void specChanged(ListChangeListener.Change change) {
    if (timingDiagramCollectionController != null) {
      timingDiagramCollectionController.setActivated(false);
    }
  }

  private void onConcreteInstanceChanged(ConcreteSpecification newVal) {
    if (getConcreteSpecification() == null) {
      view.setEmptyDiagram();
    } else {
      this.timingDiagramCollectionController =
          new TimingDiagramCollectionController(getConcreteSpecification(), selection);
      view.setDiagram(timingDiagramCollectionController.getView());

    }
  }

  private void onConcretizationActive() {
    view.setConcretizerButtonStop();
    view.getStartConcretizerButton().setOnAction(this::stopConcretizer);
  }

  private void onConcretizationInactive() {
    view.setConcretizerButtonStart();
    view.getStartConcretizerButton().setOnAction(this::startConcretizer);
  }

  private void startConcretizer(ActionEvent actionEvent) {
    ConcretizationRunner runner =
        new ConcretizationRunner(tableController.getValidator().getValidSpecification(),
            variableCollectionController.getValidator().getValidFreeVariables());
    this.concretizingTask = new JavaFxAsyncProcessTask<>(globalConfig.getSimulationTimeout(),
        runner, this.concretizationHandler);
    concretizingTask.start();

    onConcretizationActive();
  }

  private void stopConcretizer(ActionEvent actionEvent) {
    if (concretizingTask != null) {
      concretizingTask.terminate();
      concretizingTask = null;
    }
    onConcretizationInactive();
  }

  private ConcreteSpecification getConcreteSpecification() {
    return hybridSpecification.getCounterExample()
        .orElse(hybridSpecification.getConcreteInstance().orElse(null));
  }

  public SpecificationView getView() {
    return view;
  }

  private void onVerificationButtonClicked(ActionEvent actionEvent) {
    switch (stateProperty.get()) {
      case RUNNING:
        view.onVerificationButtonClicked(hybridSpecification, VerificationEvent.Type.STOP);
        break;
      default:
        view.onVerificationButtonClicked(hybridSpecification, VerificationEvent.Type.START);
    }
  }

  public HybridSpecification getSpec() {
    return spec;
  }

  private class ConcretizationTaskHandler
      implements AsyncTaskCompletedHandler<ConcreteSpecification> {
    @Override
    public void onSuccess(ConcreteSpecification concreteSpec) {
      hybridSpecification.setConcreteInstance(concreteSpec);
      timingDiagramCollectionController.setActivated(true);
      onConcretizationInactive();
    }

    @Override
    public void onException(Exception exception) {
      Alert alert = AlertFactory.createAlert(exception);
      alert.showAndWait();
      onConcretizationInactive();
    }
  }

  private class ConcretizationRunner implements AsyncRunner<ConcreteSpecification> {

    final ValidSpecification specToConcretize;
    final List<ValidFreeVariable> freeVariables;
    final SpecificationConcretizer concretizer;

    private ConcretizationRunner(ValidSpecification specToConcretize,
        List<ValidFreeVariable> freeVariables) {
      this.specToConcretize = specToConcretize;
      this.freeVariables = freeVariables;
      this.concretizer = new SmtConcretizer(globalConfig);
    }

    @Override
    public ConcreteSpecification run() throws Exception {
      return concretizer.calculateConcreteSpecification(specToConcretize, freeVariables);
    }

    @Override
    public void terminate() {
      concretizer.terminate();
    }
  }
}
