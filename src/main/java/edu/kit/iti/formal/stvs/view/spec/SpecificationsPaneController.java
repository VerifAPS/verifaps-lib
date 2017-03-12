package edu.kit.iti.formal.stvs.view.spec;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javafx.beans.binding.Bindings;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.Event;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.Tab;
import javafx.scene.control.TextInputDialog;

/**
 * Controller for {@link SpecificationsPane}. The tab logic is handled here.
 *
 * @author Carsten Csiky
 */
public class SpecificationsPaneController implements Controller {

  private final GlobalConfig globalConfig;
  private ObservableList<HybridSpecification> hybridSpecifications;
  private SpecificationsPane view;
  private ObjectProperty<VerificationState> state;
  private ObjectProperty<List<Type>> typeContext;
  private ObjectProperty<List<CodeIoVariable>> ioVariables;
  private final Map<Tab, SpecificationController> controllers;
  private final VerificationScenario scenario;

  /**
   * Creates an instance of this controller.
   *
   * @param hybridSpecifications list of the specifications t display
   * @param state the state of the verification
   * @param typeContext  available types in code
   * @param ioVariables  available variables in code
   * @param globalConfig Global config object
   * @param scenario scenario that represents what the verification needs
   */
  public SpecificationsPaneController(ObservableList<HybridSpecification> hybridSpecifications,
      ObjectProperty<VerificationState> state, ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> ioVariables, GlobalConfig globalConfig,
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
      HybridSpecification hybridSpecification =
          new HybridSpecification(new FreeVariableList(new ArrayList<>()), true);
      System.out.println(ioVariables.get());
      for (CodeIoVariable ioVariable : ioVariables.get()) {
        SpecIoVariable specIoVariable = new SpecIoVariable(ioVariable.getCategory(),
            ioVariable.getType(), ioVariable.getName());
        hybridSpecification.getColumnHeaders().add(specIoVariable);
      }
      hybridSpecifications.add(hybridSpecification);
    });

    view.getTabPane().getSelectionModel().selectedItemProperty()
        .addListener((obs, old, tab) -> onSwitchActiveTab(tab));
    onSwitchActiveTab(view.getTabPane().getSelectionModel().getSelectedItem());

    hybridSpecifications.addListener((ListChangeListener<HybridSpecification>) change -> {
      while (change.next()) {

        for (HybridSpecification addItem : change.getAddedSubList()) {
          addTab(addItem);
        }
        for (HybridSpecification spec : change.getRemoved()) {
          removeTab(change.getFrom());
        }
      }
    });
  }

  private void onTabCloseRequest(Event event, Tab tab) {
    int indexToDelete = view.getTabPane().getTabs().indexOf(tab);
    if (indexToDelete < 0) {
      return;
    }
    hybridSpecifications.remove(indexToDelete);

  }

  private void onSwitchActiveTab(Tab tab) {
    SpecificationController controller = controllers.get(tab);
    if (controller == null) {
      scenario.setActiveSpec(null);
    } else {
      scenario.setActiveSpec(controller.getSpec());
    }
  }

  private SpecificationController addTab(HybridSpecification hybridSpecification, int index) {
    final SpecificationController controller =
        new SpecificationController(typeContext, ioVariables, hybridSpecification, this.state,
            Bindings.isEmpty(scenario.getCode().syntaxErrorsProperty()).not(), globalConfig);
    Tab tab = new Tab();
    tab.setOnCloseRequest(e -> onTabCloseRequest(e, tab));
    if (hybridSpecification.isEditable()) {
      tab.setContextMenu(createTabContextMenu());
    }
    tab.textProperty().bind(hybridSpecification.nameProperty());
    tab.setContent(controller.getView());
    if (hybridSpecification.isEditable()) {
      tab.setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.EDIT));
    } else {
      tab.setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.LOCK));
    }
    view.getTabs().add(index, tab);
    controllers.put(tab, controller);
    view.getTabPane().getSelectionModel().select(tab);
    scenario.setActiveSpec(hybridSpecification);
    return controller;
  }

  public SpecificationController addTab(HybridSpecification hybridSpecification) {
    return addTab(hybridSpecification, 0);
  }

  private void onTabSetName(ActionEvent actionEvent) {
    Tab activeTab = view.getTabPane().getSelectionModel().getSelectedItem();
    ConstraintSpecification activeSpec = controllers.get(activeTab).getSpec();
    TextInputDialog textInputDialog = new TextInputDialog(activeSpec.getName());
    textInputDialog.setHeaderText("Set Specification Name");
    textInputDialog.setTitle("Specification Name");
    textInputDialog.showAndWait();
    if (textInputDialog.getResult() != null) {
      activeSpec.setName(textInputDialog.getResult());
    }
  }

  private ContextMenu createTabContextMenu() {
    ContextMenu contextMenu = new ContextMenu();
    MenuItem setNameItem = new MenuItem("Rename");
    setNameItem.setOnAction(this::onTabSetName);
    contextMenu.getItems().add(setNameItem);
    return contextMenu;
  }


  private void removeTab(int index) {
    Tab removeTab = view.getTabs().get(index);
    controllers.remove(removeTab);
    view.getTabs().remove(index);
  }


  @Override
  public SpecificationsPane getView() {
    return view;
  }
}
