package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationState;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;
import javafx.scene.control.ContextMenu;

public class SpecificationTabController implements Controller {

  private GlobalConfig globalConfig;
  private HybridSpecification spec;
  private ObjectProperty<VerificationState> stateProperty;
  private ContextMenu contextMenu;

  public SpecificationTabController(
      HybridSpecification hybridSpecification,
      ObjectProperty<VerificationState> stateProperty,
      GlobalConfig globalConfig) {
    this.spec = hybridSpecification;
    this.stateProperty = stateProperty;
    this.globalConfig = globalConfig;

  }

  public SpecificationTab getView() {
    return null;
  }


}