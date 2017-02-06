package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController;

public class TablePaneController implements Controller {

  private TablePane view;
  private Selection selection;
  private GlobalConfig globalConfig;
  private SpecificationTableController tableController;
  private VariableCollectionController variableCollection;
  private TimingDiagramCollectionController timingDiagram;

  private void onSelectionChange(Selection selection) {

  }

  public TablePaneController(HybridSpecification spec, GlobalConfig globalConfig) {
    this.globalConfig = globalConfig;
  }

  public void addIoVariable(CodeIoVariable ioVar) {
  }

  public TablePane getView() {
    return view;
  }
}
