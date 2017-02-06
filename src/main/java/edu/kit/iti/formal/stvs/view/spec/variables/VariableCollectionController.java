package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.IllegalValueTypeException;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.ComboBoxTableCell;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.DataFormat;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.util.StringConverter;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollectionController implements Controller {

  private ObservableList<Type> codeTypes;
  private FreeVariableSet freeVariableSet;
  private VariableCollection view;
  // was used for drag n drop: private int latestMouseOverRow = 0;

  private ContextMenu contextMenu;

  public VariableCollectionController(ObservableList<Type> codeTypes, FreeVariableSet freeVariableSet) {
    this.codeTypes = codeTypes;
    this.freeVariableSet = freeVariableSet;

    this.contextMenu = new ContextMenu();
    this.view = new VariableCollection();
    this.contextMenu = new ContextMenu();

    MenuItem delete = new MenuItem("Delete");
    delete.setOnAction(event -> {
      TableView<FreeVariable> tableView = view.getFreeVariableTableView();
      tableView.getItems().removeAll(tableView.getSelectionModel().getSelectedItems());
      tableView.getSelectionModel().clearSelection();
    });
    delete.setAccelerator(new KeyCodeCombination(KeyCode.DELETE));
    contextMenu.getItems().add(delete);

    view.getFreeVariableTableView().setContextMenu(contextMenu);

    view.getAddFreeVariable().setOnAction(event -> addFreeVariable());
    view.getFreeVariableTableView().setItems(freeVariableSet.getVariableSet());

    /*
    view.getFreeVariableTableView().setRowFactory(param -> {
      TableRow<FreeVariable> row = new TableRow<>();
      row.setOnMouseEntered(event -> {
        if (!row.isEmpty()) {
          System.out.println("Mouse over: " + row.getIndex());
          latestMouseOverRow = row.getIndex();
        }
      });
      return row;
    });
    */

    view.getNameTableColumn().setCellValueFactory(data -> data.getValue().nameProperty());
    view.getTypeTableColumn().setCellValueFactory(data -> data.getValue().typeProperty());
    view.getDefaultValueTableColumn().setCellValueFactory(data -> data.getValue().defaultValueProperty());

    view.getNameTableColumn().setCellFactory(TextFieldTableCell.forTableColumn());
    view.getTypeTableColumn().setCellFactory(
        ComboBoxTableCell.forTableColumn(createTypeConverter(codeTypes), codeTypes));
    view.getDefaultValueTableColumn().setCellFactory(
        TextFieldTableCell.forTableColumn(createDefaultValueConverter(codeTypes)));

    view.getNameTableColumn().setOnEditCommit(event -> {
      String proposedName = event.getNewValue();
      // It is illegal to set the variable name to be the same as another existing one
      if (!freeVariableSet.getVariableSet().stream()
          .anyMatch(var -> var.getName().equals(proposedName))) {
        try {
          event.getRowValue().setName(proposedName);
          event.consume();
        } catch (IllegalArgumentException exception) { // Invalid name
          // TODO: Provide visual error feedback
        }
      } else {
        // TODO: Provide visual error feedback
      }
      event.getTableView().refresh();
    });
    view.getTypeTableColumn().setOnEditCommit(event ->
        event.getRowValue().setType(event.getNewValue()));
    view.getDefaultValueTableColumn().setOnEditCommit(event -> {
      try {
        Value toBeSet = event.getNewValue();
        event.getRowValue().setDefaultValue(toBeSet);
        event.consume();
      } catch (IllegalValueTypeException exc) {
        // TODO: Provide visual error feedback
      }
      event.getTableView().refresh();
    });

    // TODO: Maybe fix drag n drop in future
    //configureDragAndDrop(view.getFreeVariableTableView());
  }

  private StringConverter<Type> createTypeConverter(ObservableList<Type> codeTypes) {
    return new StringConverter<Type>() {
      @Override
      public String toString(Type type) {
        return type.getTypeName();
      }
      @Override
      public Type fromString(String string) {
        return codeTypes.stream()
            .filter(type -> type.getTypeName().equals(string))
            .findFirst()
            .orElse(null);
      }
    };
  }

  private StringConverter<Value> createDefaultValueConverter(ObservableList<Type> codeTypes) {
    return new StringConverter<Value>() {
      @Override
      public String toString(Value value) {
        return value == null ? "-" : value.getValueString();
      }

      @Override
      public Value fromString(String string) {
        switch (string) {
          case "-": return null;
          default:
            try {
              Set<Type> typeContext = new HashSet<>();
              typeContext.addAll(codeTypes);
              ExpressionParser parser = new ExpressionParser("", typeContext);
              Expression parsed = parser.parseExpression(string);
              BinaryFunctionExpr bin = (BinaryFunctionExpr) parsed;
              LiteralExpr literal = (LiteralExpr) bin.getSecondArgument();
              return literal.getValue();
            } catch (Exception e) {
              // TODO: Provide visual error feedback
              return null;
            }
        }
      }
    };
  }

  private boolean containsVarWithName(String name) {
    return freeVariableSet.getVariableSet().stream()
        .anyMatch(variable -> variable.getName().equals(name));
  }

  private String findNewName() {
    int index = 0;
    final String prefix = "free_variable";
    while (containsVarWithName(prefix + index)) {
      index++;
    }
    return prefix + index;
  }

  private void addFreeVariable() {
    FreeVariable freeVariable = new FreeVariable(findNewName(), TypeBool.BOOL);
    view.getFreeVariableTableView().getItems().add(freeVariable);
  }

  @Override
  public VariableCollection getView() {
    return view;
  }

  public FreeVariableSet getFreeVariableSet() {
    return freeVariableSet;
  }

  private static final DataFormat JSON_MIME_TYPE = new DataFormat("application/json");

  /*
  private void configureDragAndDrop(TableView<FreeVariable> tableView) {
    tableView.setOnDragDetected(event -> {
      ObservableList<FreeVariable> selected = tableView.getSelectionModel().getSelectedItems();
      if (!selected.isEmpty()) {
        String serializedSelection = Json.stringFromRealFreeVariables(selected);
        Dragboard db = tableView.startDragAndDrop(TransferMode.MOVE);
        ClipboardContent cc = new ClipboardContent();
        cc.putString(serializedSelection);
        cc.put(JSON_MIME_TYPE, serializedSelection);
        db.setContent(cc);

        event.consume();
      }
    });

    tableView.setOnDragOver(event -> {
      Dragboard db = event.getDragboard();
      if (db.hasContent(JSON_MIME_TYPE)) {
        event.acceptTransferModes(TransferMode.COPY_OR_MOVE);
        event.consume();
      }
    });

    tableView.setOnDragDropped(event -> {
      Dragboard db = event.getDragboard();
      if (db.hasContent(JSON_MIME_TYPE)) {
        String dragboardContent = db.getContent(JSON_MIME_TYPE).toString();

        List<FreeVariable> droppedVariables =
            Json.stringToRealFreeVariables(codeTypes, dragboardContent);
        String source = Json.stringToSource(dragboardContent);

        if (ManagementFactory.getRuntimeMXBean().getName().equals(source)) {
          tableView.getItems().removeIf(freeVariable ->
            droppedVariables.stream()
                .anyMatch(var -> var.getName().equals(freeVariable.getName())));
        }
        tableView.getItems().addAll(latestMouseOverRow, droppedVariables);

        tableView.getSelectionModel().clearSelection();
        tableView.getSelectionModel().selectRange(
            latestMouseOverRow, latestMouseOverRow + droppedVariables.size());

        event.setDropCompleted(true);
        event.consume();
      }
    });
  }
  */

}
