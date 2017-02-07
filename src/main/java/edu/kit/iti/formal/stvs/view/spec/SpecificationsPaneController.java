package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.TabPane;

public class SpecificationsPaneController implements Controller {

  private GlobalConfig globalConfig;
  private ObservableList<HybridSpecification> hybridSpecifications;
  private TabPane view;
  private ContextMenu contextMenu;

  public SpecificationsPaneController(
      ObservableList<HybridSpecification> hybridSpecifications,
      ObjectProperty<VerificationState> state,
      GlobalConfig globalConfig) {
    this.view = new TabPane();
  }

  public TabPane getView() {
    return view;
  }

  public ObservableList<HybridSpecification> getHybridSpecifications() {
    return null;
  }

  private void addTab(HybridSpecification spec) {

  }

  private void removeTab(int tabIndex) {

  }
}
