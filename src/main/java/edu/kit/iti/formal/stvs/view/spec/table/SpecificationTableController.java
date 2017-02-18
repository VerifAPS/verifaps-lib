package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.table.problems.ColumnProblem;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.Observable;
import javafx.beans.binding.Bindings;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.*;
import javafx.scene.input.*;
import javafx.scene.layout.VBox;

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

  private final SpecificationTableView view;
  private final TableView<SynchronizedRow> tableView;
  private final HybridSpecification hybridSpec;
  private final ObjectProperty<List<Type>> typeContext;
  private final ObjectProperty<List<CodeIoVariable>> codeIoVariables;
  private final ConstraintSpecificationValidator validator;

  private final ObservableList<SynchronizedRow> data = FXCollections.observableArrayList();
  private final TableColumn<SynchronizedRow, String> durations;
  private final GlobalConfig config;

  public SpecificationTableController(GlobalConfig config,
                                      ObjectProperty<List<Type>> typeContext,
                                      ObjectProperty<List<CodeIoVariable>> codeIoVariables,
                                      ReadOnlyObjectProperty<List<ValidFreeVariable>> validVariables,
                                      HybridSpecification hybridSpecification) {
    this.config = config;
    this.tableView = new TableView<>();

    this.typeContext = typeContext;
    this.codeIoVariables = codeIoVariables;
    this.hybridSpec = hybridSpecification;
    this.validator = new ConstraintSpecificationValidator(typeContext, codeIoVariables, validVariables, hybridSpecification);
    this.durations = createViewColumn("Duration", SynchronizedRow::getDuration);

    tableView.setColumnResizePolicy(TableView.UNCONSTRAINED_RESIZE_POLICY);

    tableView.getColumns().add(durations);

    tableView.setItems(data);
    tableView.setEditable(hybridSpecification.isEditable());
    tableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
    tableView.setRowFactory(this::rowFactory);

    tableView.setContextMenu(createContextMenu());


    this.view = new SpecificationTableView(tableView);

    view.getHeader().setContextMenu(createTopLevelContextMenu());

    hybridSpecification.getColumnHeaders().forEach(this::addColumnToView);

    for (int rowIndex = 0; rowIndex < hybridSpecification.getRows().size(); rowIndex++) {
      SynchronizedRow row = new SynchronizedRow(
          hybridSpecification.getRows().get(rowIndex),
          hybridSpecification.getDurations().get(rowIndex));
      row.updateCounterExampleCells(rowIndex, hybridSpecification.getCounterExample());
      data.add(row);
    }

    data.addListener(this::onDataRowChanged);
    validator.problemsProperty().addListener((Observable o) -> onProblemsChange());
    hybridSpec.counterExampleProperty().addListener(observable -> onCounterExampleChanged());

    hybridSpec.getSelection().setOnCellClickListener(this::focusCell);
    hybridSpec.getSelection().columnProperty().addListener(this::onColumnSelectionChanged);
  }

  private void onColumnSelectionChanged(ObservableValue<? extends String> obs, String before, String columnNow) {
    if (before != null) {
      tableView.getColumns().stream()
          .filter(column -> before.equals(column.getUserData()))
          .findFirst()
          .ifPresent(column -> {
            column.getStyleClass().remove("highlighted");
          });
    }
    if (columnNow != null) {
      // If we don't clear, the gray selection could be confused with the highlighting
      tableView.getSelectionModel().clearSelection();
      tableView.getColumns().stream()
          .filter(column -> columnNow.equals(column.getUserData()))
          .findFirst()
          .ifPresent(column -> {
            column.getStyleClass().add("highlighted");
            tableView.scrollToColumn(column);
          });
    }
  }

  private void focusCell(String columnId, int row) {
    tableView.edit(row,
        tableView.getColumns().stream()
            .filter(column -> columnId.equals(column.getUserData()))
            .findFirst()
            .orElseThrow(() -> new IllegalArgumentException("Cannot focus unkown column: " + columnId)));
  }

  private void onCounterExampleChanged() {
    for (int rowIndex = 0; rowIndex < hybridSpec.getRows().size(); rowIndex++) {
      data.get(rowIndex).updateCounterExampleCells(rowIndex, hybridSpec.getCounterExample());
    }
  }

  private void onProblemsChange() {
    List<ColumnProblem> columnProblems =
        validator.problemsProperty().get().stream()
        .filter(problem -> problem instanceof ColumnProblem)
        .map(problem -> (ColumnProblem) problem)
        .collect(Collectors.toList());
    for (TableColumn<SynchronizedRow, ?> column : tableView.getColumns()) {
      if (column.getUserData() == null) {
        continue;
      }
      List<ColumnProblem> problemsForColumn = columnProblems.stream()
          .filter(problem -> problem.getColumn().equals(column.getUserData()))
          .collect(Collectors.toList());

      ColumnHeader columnHeader = (ColumnHeader) column.getGraphic();

      if (problemsForColumn.isEmpty()) {
        columnHeader.resetProblems();
      } else {
        columnHeader.configureProblems(problemsForColumn);
      }
    }
  }

  private TableCell<SynchronizedRow, String> cellFactory(TableColumn<SynchronizedRow, String> table) {
    return new SpecificationTableCell(validator);
  }

  private void onDataRowChanged(ListChangeListener.Change<? extends SynchronizedRow> change) {
    while (change.next()) {
      if (change.wasAdded()) {
        List<SpecificationRow<ConstraintCell>> rowsToBeAdded = new ArrayList<>();
        List<ConstraintDuration> durationsToBeAdded = new ArrayList<>();
        for (SynchronizedRow row : change.getAddedSubList()) {
          SpecificationRow<ConstraintCell> rowToBeAdded = row.getSourceRow();
          rowToBeAdded.commentProperty().bindBidirectional(row.commentProperty());
          rowsToBeAdded.add(rowToBeAdded);
          durationsToBeAdded.add(row.getDuration().getCell());
        }
        hybridSpec.getRows().addAll(change.getFrom(), rowsToBeAdded);
        hybridSpec.getDurations().addAll(change.getFrom(), durationsToBeAdded);
      }
      if (change.wasRemoved()) {
        hybridSpec.getRows().remove(change.getFrom(), change.getFrom() + change.getRemovedSize());
        hybridSpec.getDurations().remove(change.getFrom(), change.getFrom() + change.getRemovedSize());
      }
    }
  }

  private ContextMenu createTopLevelContextMenu() {
    MenuItem comment = new MenuItem("Comment ...");
    comment.setAccelerator(KeyCombination.keyCombination("Ctrl+k"));
    comment.setOnAction(event -> {
      new CommentPopupManager(hybridSpec, hybridSpec.isEditable(), config);
    });
    return new ContextMenu(comment);
  }

  private ContextMenu createContextMenu() {
    MenuItem insertRow = new MenuItem("Insert Row");
    MenuItem deleteRow = new MenuItem("Delete Row");
    MenuItem addNewColumn = new MenuItem("New Column...");
    MenuItem comment = new MenuItem("Comment ...");
    insertRow.setAccelerator(new KeyCodeCombination(KeyCode.INSERT));
    insertRow.setOnAction(event -> {
      int selectedIndex = tableView.getSelectionModel().getSelectedIndex();
      addEmptyRow(selectedIndex + 1);
    });
    deleteRow.setAccelerator(new KeyCodeCombination(KeyCode.DELETE));
    deleteRow.setOnAction(event ->
      data.removeAll(tableView.getSelectionModel().getSelectedItems()));
    addNewColumn.setOnAction(event ->
        new IoVariableChooserDialog(codeIoVariables, hybridSpec.getColumnHeaders())
            .showAndWait()
            .ifPresent(this::addNewColumn));
    comment.setOnAction(event -> {
      int index = tableView.getSelectionModel().getSelectedIndex();
      CommentPopupManager popupController = new CommentPopupManager(hybridSpec.getRows().get
          (index), hybridSpec.isEditable(), config);
    });
    comment.setAccelerator(KeyCodeCombination.keyCombination("Ctrl+k"));
    insertRow.disableProperty().bind(Bindings.not(tableView.editableProperty()));
    deleteRow.disableProperty().bind(Bindings.not(tableView.editableProperty()));
    addNewColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()));
    return new ContextMenu(insertRow, deleteRow, addNewColumn, comment);
  }

  private ContextMenu createColumnContextMenu(TableColumn<SynchronizedRow, ?> column) {
    MenuItem changeColumn = new MenuItem("Change Column...");
    MenuItem removeColumn = new MenuItem("Remove Column");
    MenuItem commentColumn = new MenuItem("Comment ...");
    commentColumn.setAccelerator(KeyCombination.keyCombination("Ctrl+k"));
    changeColumn.setOnAction(event -> {
      new IoVariableChangeDialog(
          hybridSpec.getColumnHeaderByName((String) column.getUserData()),
          hybridSpec.getColumnHeaders().filtered(var -> !var.getName().equals(column.getUserData())))
          .showAndWait();
    });
    removeColumn.setOnAction(event -> {
      tableView.getColumns().remove(column);
      hybridSpec.removeColumnByName((String) column.getUserData());
    });
    commentColumn.setOnAction(event -> {
      String specIoVariableName = (String) column.getUserData();
      SpecIoVariable commentable = hybridSpec.getColumnHeaderByName(specIoVariableName);
      new CommentPopupManager(commentable, tableView.isEditable(), config);
    });
    changeColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()));
    removeColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()));
    return new ContextMenu(changeColumn, removeColumn, commentColumn);
  }

  public void addEmptyRow(int index) {
    Map<String, ConstraintCell> wildcardCells = new HashMap<>();
    hybridSpec.getColumnHeaders().forEach(specIoVariable ->
        wildcardCells.put(specIoVariable.getName(), new ConstraintCell("-")));
    SpecificationRow<ConstraintCell> wildcardRow = ConstraintSpecification.createRow(wildcardCells);
    data.add(index, new SynchronizedRow(wildcardRow, new ConstraintDuration("1")));
  }

  public void addNewColumn(SpecIoVariable specIoVariable) {
    // Add column to model:
    if (data.isEmpty()) {
      hybridSpec.getColumnHeaders().add(specIoVariable);
    } else {
      SpecificationColumn<ConstraintCell> dataColumn = new SpecificationColumn<>(
          data.stream().map(row -> new ConstraintCell("-")).collect(Collectors.toList()));
      hybridSpec.addColumn(specIoVariable, dataColumn);
    }

    // Add column to view:
    addColumnToView(specIoVariable);
  }

  private void addColumnToView(final SpecIoVariable specIoVariable) {
    TableColumn<SynchronizedRow, String> column = createViewColumn(
        specIoVariable.getName(),
        synchronizedRow -> synchronizedRow.getCells().get(specIoVariable.getName()));

    column.setUserData(specIoVariable.getName());
    specIoVariable.nameProperty().addListener(
        (Observable o) -> column.setUserData(specIoVariable.getName()));
    column.setText("");
    column.setGraphic(new ColumnHeader(specIoVariable));
    column.setPrefWidth(specIoVariable.getColumnConfig().getWidth());
    column.widthProperty().addListener((obs, old, newVal) ->
        specIoVariable.getColumnConfig().setWidth(newVal.doubleValue()));
    column.setContextMenu(createColumnContextMenu(column));

    tableView.getColumns().add(tableView.getColumns().size() - 1, column);
  }

  private TableColumn<SynchronizedRow, String> createViewColumn(
      String colName,
      final Function<SynchronizedRow, HybridCellModel<?>> extractCellFromRow) {
    TableColumn<SynchronizedRow, String> column = new TableColumn<>(colName);
    column.setSortable(false);
    column.setEditable(true);
    column.setPrefWidth(100);
    column.setCellFactory(this::cellFactory);

    column.setCellValueFactory(rowModelData ->
        extractCellFromRow.apply(rowModelData.getValue())
            .stringRepresentationProperty());

    return column;
  }

  private static final DataFormat SERIALIZED_MIME_TYPE = new DataFormat("application/x-java-serialized-object");

  // from: http://stackoverflow.com/questions/28603224/sort-tableview-with-drag-and-drop-rows
  // TODO: Have fun? Implement dragging multiple rows, from one program to another, etc.
  private TableRow<SynchronizedRow> rowFactory(TableView<SynchronizedRow> tableView) {
    TableRow<SynchronizedRow> row = new TableRow<SynchronizedRow>() {
      {
        hybridSpec.getSelection().rowProperty().addListener(this::rowSelectionChanged);
      }

      private void rowSelectionChanged(ObservableValue<? extends Integer> obs, Integer before, Integer now) {
        if (before != null && getIndex() == before) {
          getStyleClass().remove ("highlighted");
        }
        if (now != null && getIndex() == now) {
          getStyleClass().add("highlighted");
          tableView.scrollTo(getIndex());
        }
      }
    };

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
        if (tableView.isEditable() && row.getIndex() != (Integer) db.getContent(SERIALIZED_MIME_TYPE)) {
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
  public SpecificationTableView getView() {
    return view;
  }

  public HybridSpecification getHybridSpecification() {
    return hybridSpec;
  }

  public ConstraintSpecificationValidator getValidator() {
    return this.validator;
  }
}
