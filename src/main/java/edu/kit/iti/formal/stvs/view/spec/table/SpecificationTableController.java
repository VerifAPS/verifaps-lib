package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.ClipboardContent;
import javafx.scene.input.DataFormat;
import javafx.scene.input.Dragboard;
import javafx.scene.input.TransferMode;

import java.util.function.Function;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SpecificationTableController implements Controller {

  private static final DataFormat SERIALIZED_MIME_TYPE = new DataFormat("application/x-java-serialized-object");

  private final TableView<HybridRowModel> tableView;

  private final ObservableList<HybridRowModel> data = FXCollections.observableArrayList();
  private final TableColumn<HybridRowModel, String> inputColumn;
  private final TableColumn<HybridRowModel, String> outputColumn;
  private final TableColumn<HybridRowModel, String> durations;

  public SpecificationTableController() {
    this.tableView = new TableView<>();
    this.inputColumn = new TableColumn<>("Input");
    this.outputColumn = new TableColumn<>("Output");
    this.durations = createColumn("Duration", HybridRowModel::getDuration);

    inputColumn.setContextMenu(createColumnContextMenu(VariableCategory.INPUT));
    outputColumn.setContextMenu(createColumnContextMenu(VariableCategory.OUTPUT));

    tableView.getColumns().addAll(inputColumn, outputColumn, durations);

    tableView.setItems(data);
    tableView.setEditable(true);
    tableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
    tableView.setRowFactory(this::rowFactory);

    createTableContextMenu();
  }

  private void createTableContextMenu() {
    MenuItem insertRow = new MenuItem("Insert Row");
    MenuItem deleteRow = new MenuItem("Delete Row");
    insertRow.setOnAction(event -> {
      int selectedIndex = tableView.getSelectionModel().getSelectedIndex();
      tableView.getItems().add(selectedIndex + 1, createEmptyRow());
    });
    deleteRow.setOnAction(event ->
      tableView.getItems().removeAll(tableView.getSelectionModel().getSelectedItems()));
    ContextMenu globalCM = new ContextMenu(insertRow, deleteRow);

    tableView.setContextMenu(globalCM);
  }

  private HybridRowModel createEmptyRow() {
    HybridRowModel row = new HybridRowModel("-");
    inputColumn.getColumns().forEach(hybridRowModelTableColumn ->
      row.add(hybridRowModelTableColumn.getText(), "-")
    );
    outputColumn.getColumns().forEach(hybridRowModelTableColumn ->
        row.add(hybridRowModelTableColumn.getText(), "-")
    );
    return row;
  }

  private ContextMenu createColumnContextMenu(VariableCategory category) {
    ContextMenu menu = new ContextMenu();
    MenuItem addNewColumn = new MenuItem("New Column...");
    addNewColumn.setOnAction(event -> addColumn(category, "TODO"));
    menu.getItems().addAll(addNewColumn);
    return menu;
  }

  private TableColumn<HybridRowModel, String> createColumn(
      String colName,
      final Function<HybridRowModel, HybridCellModel> extractCellFromRow) {
    TableColumn<HybridRowModel, String> column = new TableColumn<>(colName);
    column.setSortable(false);
    column.setEditable(true);
    column.setPrefWidth(100);

    column.setCellFactory(TextFieldTableCell.forTableColumn());
    column.setCellValueFactory(rowModelData ->
        extractCellFromRow.apply(rowModelData.getValue())
            .stringRepresentationProperty());

    return column;
  }

  private TableColumn<HybridRowModel, String> getColumnFromCategory(VariableCategory category) {
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
    TableColumn<HybridRowModel, String> column = getColumnFromCategory(category);
    addNewColumnToCategory(column, columnHeader);
    final HybridCellModel dontcare = new HybridCellModel(new ConstraintDuration("-"));
    data.forEach(hybridRowModel -> hybridRowModel.put(columnHeader, dontcare));
  }

  public void addRow(HybridRowModel row) {
    data.add(row);
  }

  private void addNewColumnToCategory(TableColumn<HybridRowModel, String> column, final String columnName) {
    column.getColumns().add(
        createColumn(
            columnName,
            hybridRowModel -> hybridRowModel.getCellForVariable(columnName))
    );
  }

  // from: http://stackoverflow.com/questions/28603224/sort-tableview-with-drag-and-drop-rows
  // TODO: Have fun? Implement dragging multiple rows, from one program to another, etc.
  private TableRow<HybridRowModel> rowFactory(TableView<HybridRowModel> tableView) {
    TableRow<HybridRowModel> row = new TableRow<>();

    row.setOnDragDetected(event -> {
      if (! row.isEmpty()) {
        Integer index = row.getIndex();
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
        HybridRowModel draggedRow = tableView.getItems().remove(draggedIndex);

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
}
