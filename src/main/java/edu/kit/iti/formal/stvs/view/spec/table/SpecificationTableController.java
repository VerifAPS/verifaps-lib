package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.util.MapUtil;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SpecificationTableController implements Controller {

  private static final DataFormat SERIALIZED_MIME_TYPE = new DataFormat("application/x-java-serialized-object");

  private final TableView<SynchronizedRow> tableView;
  private final HybridSpecification tableData;

  private final ObservableList<SynchronizedRow> data = FXCollections.observableArrayList();
  private final TableColumn<SynchronizedRow, String> inputColumn;
  private final TableColumn<SynchronizedRow, String> outputColumn;
  private final TableColumn<SynchronizedRow, String> durations;

  public SpecificationTableController(ObservableSet<Type> typeContext,
                                      ObservableSet<CodeIoVariable> codeIoVariables,
                                      FreeVariableSet freeVariableSet) {
    this.tableView = new TableView<>();
    this.tableData = new HybridSpecification(typeContext, codeIoVariables, freeVariableSet, true);
    this.inputColumn = new TableColumn<>("Input");
    this.outputColumn = new TableColumn<>("Output");
    this.durations = createColumn("Duration", SynchronizedRow::getDuration);

    inputColumn.setContextMenu(createColumnContextMenu(VariableCategory.INPUT));
    outputColumn.setContextMenu(createColumnContextMenu(VariableCategory.OUTPUT));

    tableView.getColumns().addAll(inputColumn, outputColumn, durations);

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
        tableData.getRows().addAll(change.getFrom(), rowsToBeAdded);
        tableData.getDurations().addAll(change.getFrom(), durationsToBeAdded);
      }
      if (change.wasRemoved()) {
        tableData.getRows().remove(change.getFrom(), change.getFrom() + change.getRemovedSize());
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
    tableData.getSpecIoVariables().forEach(specIoVariable ->
        wildcardCells.put(specIoVariable.getName(), new ConstraintCell("-")));
    SpecificationRow<ConstraintCell> wildcardRow = new SpecificationRow<>(wildcardCells);
    data.add(index, new SynchronizedRow(wildcardRow, new ConstraintDuration("-")));
  }

  private ContextMenu createColumnContextMenu(VariableCategory category) {
    ContextMenu menu = new ContextMenu();
    MenuItem addNewColumn = new MenuItem("New Column...");
    addNewColumn.setOnAction(event -> addColumn(category, "TODO"));
    menu.getItems().addAll(addNewColumn);
    return menu;
  }

  private TableColumn<SynchronizedRow, String> createColumn(
      String colName,
      final Function<SynchronizedRow, HybridCellModel> extractCellFromRow) {
    TableColumn<SynchronizedRow, String> column = new TableColumn<>(colName);
    column.setSortable(false);
    column.setEditable(true);
    column.setPrefWidth(100);

    column.setCellFactory(TextFieldTableCell.forTableColumn());
    column.setCellValueFactory(rowModelData ->
        extractCellFromRow.apply(rowModelData.getValue())
            .stringRepresentationProperty());

    return column;
  }

  private TableColumn<SynchronizedRow, String> getColumnFromCategory(VariableCategory category) {
    switch (category) {
      case INPUT:
        return inputColumn;
      case OUTPUT:
        return outputColumn;
      default:
        throw new IllegalArgumentException("Unkown VariableCategory: " + category);
    }
  }

  public void addColumn(VariableCategory category, String columnHeader) {
    // Add column to view:
    TableColumn<SynchronizedRow, String> viewColumn = getColumnFromCategory(category);
    addNewColumnToCategory(viewColumn, columnHeader);

    // Add column to model:
    SpecIoVariable specIoVariable = new SpecIoVariable(category, TypeInt.INT, columnHeader);
    if (data.isEmpty()) {
      tableData.getSpecIoVariables().add(specIoVariable);
    } else {
      SpecificationColumn<ConstraintCell> dataColumn = new SpecificationColumn<>(
          data.stream().map(row -> new ConstraintCell("-")).collect(Collectors.toList()));
      tableData.addColumn(specIoVariable, dataColumn);
    }
  }

  private void addNewColumnToCategory(TableColumn<SynchronizedRow, String> column, final String columnName) {
    column.getColumns().add(
        createColumn(
            columnName,
            synchronizedRow -> synchronizedRow.getCells().get(columnName))
    );
  }

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
        if (row.getIndex() != ((Integer)db.getContent(SERIALIZED_MIME_TYPE)).intValue()) {
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
    return tableData;
  }
}
