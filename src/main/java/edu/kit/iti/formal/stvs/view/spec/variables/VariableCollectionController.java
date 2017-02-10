package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.util.ListTypeConverter;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.util.StringConverter;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollectionController implements Controller {

  private ObjectProperty<List<Type>> codeTypes;
  private FreeVariableList freeVariableList;
  private FreeVariableListValidator validator;
  private VariableCollection view;
  // was used for drag n drop: private int latestMouseOverRow = 0;

  private ContextMenu contextMenu;

  public VariableCollectionController(ObjectProperty<List<Type>> codeTypes,
                                      FreeVariableList freeVariableList) {
    this.codeTypes = codeTypes;
    this.freeVariableList = freeVariableList;
    this.validator = new FreeVariableListValidator(codeTypes, freeVariableList);

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
    view.getFreeVariableTableView().setItems(freeVariableList.getVariables());

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

    ObservableList<Type> codeTypesList = ListTypeConverter.makeObservableList(codeTypes);
    view.getNameTableColumn().setCellFactory(TextFieldTableCell.forTableColumn());
    view.getTypeTableColumn().setCellFactory(TextFieldTableCell.forTableColumn()); // TODO: Make this combo box again!
    view.getDefaultValueTableColumn().setCellFactory(TextFieldTableCell.forTableColumn());
    // TODO: Show FreeVariableProblems!!!

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

  private void addFreeVariable() {
    FreeVariable freeVariable = new FreeVariable("", "");
    view.getFreeVariableTableView().getItems().add(freeVariable);
  }

  @Override
  public VariableCollection getView() {
    return view;
  }

  public FreeVariableList getFreeVariableList() {
    return freeVariableList;
  }

  public FreeVariableListValidator getValidator() {
    return validator;
  }

  /*
  private static final DataFormat JSON_MIME_TYPE = new DataFormat("application/json");

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
