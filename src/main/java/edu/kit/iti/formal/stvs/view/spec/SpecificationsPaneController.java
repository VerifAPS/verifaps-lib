package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.IoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.binding.Bindings;
import javafx.beans.binding.BooleanBinding;
import javafx.beans.property.BooleanProperty;
import javafx.application.Platform;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Tab;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SpecificationsPaneController implements Controller {

  private final GlobalConfig globalConfig;
  private ObservableList<HybridSpecification> hybridSpecifications;
  private SpecificationsPane view;
  private ContextMenu contextMenu;
  private ObjectProperty<VerificationState> state;
  private ObjectProperty<List<Type>> typeContext;
  private ObjectProperty<List<CodeIoVariable>> ioVariables;
  private final Map<Tab, SpecificationController> controllers;
  private final VerificationScenario scenario;

  public SpecificationsPaneController(
      ObservableList<HybridSpecification> hybridSpecifications,
      ObjectProperty<VerificationState> state,
      ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> ioVariables,
      GlobalConfig globalConfig,
      VerificationScenario scenario) {
    this.view = new SpecificationsPane();
    this.globalConfig = globalConfig;
    this.scenario = scenario;
    this.state = state;
    this.controllers = new HashMap<>();
    this.typeContext = typeContext;
    this.ioVariables = ioVariables;
    this.hybridSpecifications = hybridSpecifications;

    hybridSpecifications.forEach(this::addTab);
    this.view.onTabAdded(() -> {
      HybridSpecification hybridSpecification = new HybridSpecification(
          new FreeVariableList(new ArrayList<>()), true);
      for (CodeIoVariable ioVariable : ioVariables.get()) {
        SpecIoVariable specIoVariable = new SpecIoVariable(ioVariable.getCategory(), ioVariable
            .getType(), ioVariable.getName());
        hybridSpecification.getColumnHeaders().add(specIoVariable);
      }
      hybridSpecifications.add(hybridSpecification);

    });

    view.getTabPane().getSelectionModel().selectedItemProperty().addListener((obs, old, tab)
        -> switchActiveTab(tab));
    switchActiveTab(view.getTabPane().getSelectionModel().getSelectedItem());

    hybridSpecifications.addListener((ListChangeListener<HybridSpecification>) change -> {
      while (change.next()) {

        for (HybridSpecification addItem : change.getAddedSubList()) {
          addTab(addItem);
        }
        for (HybridSpecification spec : change.getRemoved()) {
          removeTab(spec);
        }
      }
    });
  }

  private void switchActiveTab(Tab tab) {
    SpecificationController controller = controllers.get(tab);
    if (controller == null) {
      scenario.setActiveSpec(null);
    } else {
      scenario.setActiveSpec(controller.getSpec());
    }
  }

  private SpecificationController addTab(HybridSpecification hybridSpecification, int index) {
    SpecificationController controller = new SpecificationController(
        typeContext, ioVariables, hybridSpecification, this.state,
        Bindings.isEmpty(scenario.getCode().syntaxErrorsProperty()).not(), globalConfig);
    Tab tab = new Tab();
    String editable = hybridSpecification.isEditable() ? "" : " [locked]";
    tab.setText(hybridSpecification.getName() + editable);
    tab.setContent(controller.getView());
    view.getTabs().add(index, tab);
    controllers.put(tab, controller);
    view.getTabPane().getSelectionModel().select(tab);
    return controller;
  }

  public SpecificationController addTab(HybridSpecification hybridSpecification) {
    return addTab(hybridSpecification, 0);
  }


  private void removeTab(HybridSpecification specification) {
    view.getTabs().removeIf(tab -> {
      if (controllers.get(tab) != null) {
        SpecificationController removedController = controllers.remove(tab);
        return true; //yeah... I know
      }
      return false;
    });
  }


  @Override
  public SpecificationsPane getView() {
    return view;
  }
}
