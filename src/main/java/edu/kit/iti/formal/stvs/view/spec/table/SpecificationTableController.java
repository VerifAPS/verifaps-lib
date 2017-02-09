package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.table.problems.CellProblem;
import edu.kit.iti.formal.stvs.model.table.problems.DurationProblem;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblemRecognizer;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.WeakInvalidationListener;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.*;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.util.converter.DefaultStringConverter;

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

  private static final String DURATION_COL_USER_DATA = "__ duration column";

  private final TableView<SynchronizedRow> tableView;
  private final HybridSpecification hybridSpec;
  private final ObjectProperty<List<Type>> typeContext;
  private final ObjectProperty<List<CodeIoVariable>> codeIoVariables;
  private final SpecProblemRecognizer problemRecognizer;

  private final ObservableList<SynchronizedRow> data = FXCollections.observableArrayList();
  private final TableColumn<SynchronizedRow, String> durations;
  private final ContextMenu columnContextMenu;

  public SpecificationTableController(ObjectProperty<List<Type>> typeContext,
                                      ObjectProperty<List<CodeIoVariable>> codeIoVariables,
                                      ReadOnlyObjectProperty<List<ValidFreeVariable>> validVariables,
                                      HybridSpecification hybridSpecification) {
    this.tableView = new TableView<>();

    this.typeContext = typeContext;
    this.codeIoVariables = codeIoVariables;
    this.hybridSpec = hybridSpecification;
    this.problemRecognizer = new SpecProblemRecognizer(typeContext, codeIoVariables, validVariables, hybridSpecification);
    this.durations = createViewColumn(DURATION_COL_USER_DATA, "Duration", SynchronizedRow::getDuration);
    this.columnContextMenu = createColumnEditingContextMenu();

    durations.setContextMenu(columnContextMenu);
    tableView.getColumns().add(durations);

    tableView.setItems(data);
    tableView.setEditable(true);
    tableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
    tableView.setRowFactory(this::rowFactory);


    tableView.setContextMenu(createRowEditingContextMenu());

    tableView.getStylesheets().add(SpecificationTableController.class.getResource("style.css").toExternalForm());

    hybridSpecification.getColumnHeaders().forEach(this::addColumnToView);

    for (int rowIndex = 0; rowIndex < hybridSpecification.getRows().size(); rowIndex++) {
      data.add(new SynchronizedRow(
          hybridSpecification.getRows().get(rowIndex),
          hybridSpecification.getDurations().get(rowIndex)));
    }

    data.addListener(this::onDataRowChanged);
  }

  private TableCell<SynchronizedRow, String> cellFactory(TableColumn<SynchronizedRow, String> table) {
    return new TextFieldTableCell<SynchronizedRow, String>(new DefaultStringConverter()) {
      private final WeakInvalidationListener onProblemChangeListener;
      private final Paint normalTextFill;
      {
        normalTextFill = getTextFill();
        onProblemChangeListener = new WeakInvalidationListener(observable -> this.onProblemsChanged());
        problemRecognizer.problemsProperty().addListener(onProblemChangeListener);
        getStyleClass().add("spec-cell");
      }

      private void configureProblem(SpecProblem problem) {
        getStyleClass().remove("spec-cell-problem");
        getStyleClass().add("spec-cell-problem");
        setTextFill(Color.RED);
        setTooltip(new Tooltip(problem.getErrorMessage()));
      }

      private void resetCellVisuals() {
        setTextFill(normalTextFill);
        getStyleClass().remove("spec-cell-problem");
        setTooltip(null);
      }

      private void onProblemsChanged() {
        if (!isEmpty()) {
          List<SpecProblem> problems = problemRecognizer.problemsProperty().get();
          for (SpecProblem problem : problems) {
            if (problem instanceof CellProblem) {
              CellProblem cellProblem = (CellProblem) problem;
              String col = cellProblem.getColumn();
              if (col.equals(getTableColumn().getUserData()) && cellProblem.getRow() == getTableRow().getIndex()) {
                configureProblem(problem);
                return;
              }
            } else if (problem instanceof DurationProblem) {
              DurationProblem durationProblem = (DurationProblem) problem;
              if (DURATION_COL_USER_DATA.equals(getTableColumn().getUserData()) && durationProblem.getRow() == getTableRow().getIndex()) {
                configureProblem(problem);
                return;
              }
            }
          }
        }
        resetCellVisuals();
      }

    };
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

  private ContextMenu createRowEditingContextMenu() {
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
    return new ContextMenu(insertRow, deleteRow);
  }

  private ContextMenu createColumnEditingContextMenu() {
    ContextMenu menu = new ContextMenu();
    MenuItem addNewColumn = new MenuItem("New Column...");
    addNewColumn.setOnAction(event ->
        new IoVariableNameDialog(typeContext, codeIoVariables)
          .showAndWait()
          .ifPresent(this::addNewColumn));
    menu.getItems().addAll(addNewColumn);
    return menu;
  }

  public void addEmptyRow(int index) {
    Map<String, ConstraintCell> wildcardCells = new HashMap<>();
    hybridSpec.getColumnHeaders().forEach(specIoVariable ->
        wildcardCells.put(specIoVariable.getName(), new ConstraintCell("-")));
    SpecificationRow<ConstraintCell> wildcardRow = ConstraintSpecification.createRow(wildcardCells);
    data.add(index, new SynchronizedRow(wildcardRow, new ConstraintDuration("-")));
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
    tableView.getColumns().add(0,
        createViewColumn(
            specIoVariable.getName(),
            specIoVariable.getVarDescriptor(),
            synchronizedRow -> synchronizedRow.getCells().get(specIoVariable.getName()))
    );
    tableView.refresh(); // TODO: maybe this is not needed with the new deep observable updates in the model
  }

  private TableColumn<SynchronizedRow, String> createViewColumn(
      String colIndex,
      String colName,
      final Function<SynchronizedRow, HybridCellModel> extractCellFromRow) {
    TableColumn<SynchronizedRow, String> column = new TableColumn<>(colName);
    column.setSortable(false);
    column.setEditable(true);
    column.setPrefWidth(150);
    column.setContextMenu(columnContextMenu);
    column.setCellFactory(this::cellFactory);
    column.setUserData(colIndex);

    //column.setCellFactory(TextFieldTableCell.forTableColumn());
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
  public TableView<SynchronizedRow> getView() {
    return tableView;
  }

  public HybridSpecification getHybridSpecification() {
    return hybridSpec;
  }
}
