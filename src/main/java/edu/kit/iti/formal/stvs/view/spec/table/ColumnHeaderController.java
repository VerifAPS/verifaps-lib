package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

public class ColumnHeaderController implements Controller {
  private ColumnHeader columnHeader;
  private final ObservableList<CodeIoVariable> codeVars;
  private final ObjectProperty<SpecIoVariable> columnName;
  private GlobalConfig globalConfig;
  private ContextMenu contextMenu;
  private ObservableList<Type> types;

  public ColumnHeaderController(ObservableList<Type> types, ObservableList<CodeIoVariable> codeVars, ObjectProperty<SpecIoVariable> columnName, GlobalConfig globalConfig) {
    this.types = types;
    this.codeVars = codeVars;
    this.columnName = columnName;
    this.globalConfig = globalConfig;
  }

  @Override
  public ColumnHeader getView() {
    return columnHeader;
  }
}
