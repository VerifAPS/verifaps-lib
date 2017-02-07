package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.util.MapUtil;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SpecificationTableController implements Controller {

  private final TableView<SynchronizedRow> tableView;
  private final HybridSpecification hybridSpec;

  private final ObservableList<SynchronizedRow> data = FXCollections.observableArrayList();
  private final TableColumn<SynchronizedRow, String> durations;
  private final ContextMenu columnContextMenu;

  public SpecificationTableController(ObjectProperty<List<Type>> typeContext,
                                      ObjectProperty<List<CodeIoVariable>> codeIoVariables,
                                      FreeVariableSet freeVariableSet) {
    this.tableView = new TableView<>();
    this.hybridSpec = new HybridSpecification(typeContext, codeIoVariables, freeVariableSet, true);
    this.durations = createColumn("Duration", SynchronizedRow::getDuration);
    this.columnContextMenu = createColumnContextMenu();

    durations.setContextMenu(columnContextMenu);
    tableView.getColumns().add(durations);

    tableView.setItems(data);
    tableView.setEditable(true);
    tableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
    tableView.setRowFactory(this::rowFactory);

    data.addListener(this::onDataRowChanged);

    createTableContextMenu();
  }

  private void onDataRowChanged(ListChangeListener.Change<? extends SynchronizedRow> change) {
    while (change.next()) {
      if (change.wasAdded()) {
        List<SpecificationRow<ConstraintCell>> rowsToBeAdded = new ArrayList<>();
        List<ConstraintDuration> durationsToBeAdded = new ArrayList<>();
        for (SynchronizedRow row : change.getAddedSubList()) {
          Map<String, ConstraintCell> cells = MapUtil.mapValues(row.getCells(), HybridCellModel::getCell);
          SpecificationRow<ConstraintCell> rowToBeAdded = new SpecificationRow<>(cells);
          rowToBeAdded.commentProperty().bindBidirectional(row.commentProperty());
          rowsToBeAdded.add(rowToBeAdded);
          durationsToBeAdded.add(row.getDuration().getCell());
        }
        hybridSpec.getRows().addAll(change.getFrom(), rowsToBeAdded);
        hybridSpec.getDurations().addAll(change.getFrom(), durationsToBeAdded);
      }
      if (change.wasRemoved()) {
        hybridSpec.getRows().remove(change.getFrom(), change.getFrom() + change.getRemovedSize());
      }
    }
  }

  private void createTableContextMenu() {
    MenuItem insertRow = new MenuItem("Insert Row");
    MenuItem deleteRow = new MenuItem("Delete Row");
    insertRow.setAccelerator(new KeyCodeCombination(KeyCode.INSERT));
    insertRow.setOnAction(event -> {
      int selectedIndex = tableView.getSelectionModel().getSelectedIndex();
      addEmptyRow(selectedIndex + 1);
    });
    deleteRow.setAccelerator(new KeyCodeCombination(KeyCode.DELETE));
    deleteRow.setOnAction(event ->
      data.removeAll(tableView.getSelectionModel().getSelectedItems()));
    ContextMenu globalCM = new ContextMenu(insertRow, deleteRow);

    tableView.setContextMenu(globalCM);
  }

  public void addEmptyRow(int index) {
    Map<String, ConstraintCell> wildcardCells = new HashMap<>();
    hybridSpec.getSpecIoVariables().forEach(specIoVariable ->
        wildcardCells.put(specIoVariable.getName(), new ConstraintCell("-")));
    SpecificationRow<ConstraintCell> wildcardRow = new SpecificationRow<>(wildcardCells);
    data.add(index, new SynchronizedRow(wildcardRow, new ConstraintDuration("-")));
  }

  private ContextMenu createColumnContextMenu() {
    ContextMenu menu = new ContextMenu();
    MenuItem addNewColumn = new MenuItem("New Column...");
    addNewColumn.setOnAction(event -> {
      new IoVariableNameDialog(hybridSpec.typeContextProperty(), hybridSpec.codeIoVariablesProperty())
          .showAndWait()
          .ifPresent(this::addColumn);
    });
    menu.getItems().addAll(addNewColumn);
    return menu;
  }

  public void addColumn(SpecIoVariable specIoVariable) {
    // Add column to view:
    addNewColumn(specIoVariable.getName());

    // Add column to model:
    hybridSpec.getSpecIoVariables().add(specIoVariable);
    if (!data.isEmpty()) {
      SpecificationColumn<ConstraintCell> dataColumn = new SpecificationColumn<>(
          data.stream().map(row -> new ConstraintCell("-")).collect(Collectors.toList()));
      hybridSpec.addColumn(specIoVariable, dataColumn);
    }
  }

  private void addNewColumn(final String columnName) {
    tableView.getColumns().add(0,
        createColumn(
            columnName,
            synchronizedRow -> synchronizedRow.getCells().get(columnName))
    );
    tableView.refresh();
  }

  private TableColumn<SynchronizedRow, String> createColumn(
      String colName,
      final Function<SynchronizedRow, HybridCellModel> extractCellFromRow) {
    TableColumn<SynchronizedRow, String> column = new TableColumn<>(colName);
    column.setSortable(false);
    column.setEditable(true);
    column.setPrefWidth(100);
    column.setContextMenu(columnContextMenu);

    column.setCellFactory(TextFieldTableCell.forTableColumn());
    column.setCellValueFactory(rowModelData ->
        extractCellFromRow.apply(rowModelData.getValue())
            .stringRepresentationProperty());

    return column;
  }

  private static final DataFormat SERIALIZED_MIME_TYPE = new DataFormat("application/x-java-serialized-object");

  // from: http://stackoverflow.com/questions/28603224/sort-tableview-with-drag-and-drop-rows
  // TODO: Have fun? Implement dragging multiple rows, from one program to another, etc.
  private TableRow<SynchronizedRow> rowFactory(TableView<SynchronizedRow> tableView) {
    TableRow<SynchronizedRow> row = new TableRow<>();

    row.setOnDragDetected(event -> {
      if (!row.isEmpty()) {
        Integer index = row.getIndex();
        tableView.getSelectionModel().clearAndSelect(index);
        Dragboard db = row.startDragAndDrop(TransferMode.MOVE);
        db.setDragView(row.snapshot(null, null));
        ClipboardContent cc = new ClipboardContent();
        cc.put(SERIALIZED_MIME_TYPE, index);
        db.setContent(cc);
        event.consume();
      }
    });

    row.setOnDragOver(event -> {
      Dragboard db = event.getDragboard();
      if (db.hasContent(SERIALIZED_MIME_TYPE)) {
        if (row.getIndex() != (Integer) db.getContent(SERIALIZED_MIME_TYPE)) {
          event.acceptTransferModes(TransferMode.COPY_OR_MOVE);
          event.consume();
        }
      }
    });

    row.setOnDragDropped(event -> {
      Dragboard db = event.getDragboard();
      if (db.hasContent(SERIALIZED_MIME_TYPE)) {
        int draggedIndex = (Integer) db.getContent(SERIALIZED_MIME_TYPE);
        SynchronizedRow draggedRow = tableView.getItems().remove(draggedIndex);

        int dropIndex ;

        if (row.isEmpty()) {
          dropIndex = tableView.getItems().size() ;
        } else {
          dropIndex = row.getIndex();
        }

        tableView.getItems().add(dropIndex, draggedRow);

        event.setDropCompleted(true);
        tableView.getSelectionModel().clearAndSelect(dropIndex);
        event.consume();
      }
    });

    return row;
  }

  @Override
  public TableView getView() {
    return tableView;
  }

  public HybridSpecification getData() {
    return hybridSpec;
  }
}
