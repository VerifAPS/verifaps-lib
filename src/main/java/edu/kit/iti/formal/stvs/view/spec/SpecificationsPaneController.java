package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SpecificationsPaneController implements Controller {

  private ObservableList<HybridSpecification> hybridSpecifications;
  private SpecificationsPane view;
  private ContextMenu contextMenu;
  private ObjectProperty<VerificationState> state;
  private ObjectProperty<List<Type>> typeContext;
  private final Map<Tab, SpecificationController> controllers;

  public SpecificationsPaneController(
      ObservableList<HybridSpecification> hybridSpecifications,
      ObjectProperty<VerificationState> state,
      ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> ioVariables) {
    this.view = new SpecificationsPane();
    this.state = state;
    this.controllers = new HashMap<>();
    this.typeContext = typeContext;
    this.hybridSpecifications = hybridSpecifications;

    hybridSpecifications.forEach(this::addTab);
    this.view.onTabAdded(() -> {
      hybridSpecifications.add(new HybridSpecification(typeContext, ioVariables, new
          FreeVariableSet(), true));
    });

    hybridSpecifications.addListener(new ListChangeListener<HybridSpecification>() {
      @Override
      public void onChanged(Change<? extends HybridSpecification> change) {
        while(change.next()) {

          for (HybridSpecification addItem : change.getAddedSubList()) {
            addTab(addItem);
          }
          for (HybridSpecification spec : change.getRemoved()) {
            removeTab(spec);
          }
        }
      }
    });
  }

  private SpecificationController addTab(HybridSpecification hybridSpecification, int index) {
    SpecificationController controller = new SpecificationController(hybridSpecification, this.state);
    Tab tab = new Tab();
    String editable = hybridSpecification.isEditable() ? "" : "locked";
    tab.setText("Specification " + editable);
    System.out.println(controller.getView());
    tab.setContent(controller.getView());
    view.getTabs().add(index, tab);
    controllers.put(tab, controller);
    return controller;
  }

  private SpecificationController addTab(HybridSpecification hybridSpecification) {
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

  public ObservableList<HybridSpecification> getHybridSpecifications() {
    return null;
  }

  private void removeTab(int tabIndex) {

  }
}
