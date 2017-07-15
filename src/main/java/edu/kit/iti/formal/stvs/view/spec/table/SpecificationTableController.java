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
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.beans.Observable;
import javafx.beans.binding.Bindings;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.*;
import javafx.scene.input.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * The controller for the {@link SpecificationTableView}. Orchestrates complex user interactions on
 * the view (such as dragging and dropping of rows, selecting columns and cells etc.) and trigger
 * updates on the model (the underlying {@link HybridSpecification}).
 *
 * @author Philipp
 */
public class SpecificationTableController implements Controller {
    public static final Logger LOGGER = LoggerFactory.getLogger(SpecificationTableController.class);

    private static final DataFormat SERIALIZED_MIME_TYPE =
            new DataFormat("application/x-java-serialized-object");
    private final SpecificationTableView view;
    private final TableView<HybridRow> tableView;
    private final HybridSpecification hybridSpec;
    private final ObjectProperty<List<Type>> typeContext;
    private final ObjectProperty<List<CodeIoVariable>> codeIoVariables;
    private final ConstraintSpecificationValidator validator;
    private final TableColumn<HybridRow, String> durations;
    private final GlobalConfig config;

    /**
     * Create a new SpecificationTableController.
     *
     * @param config              A reference to the current {@link GlobalConfig}
     * @param typeContext         A list of the currently defined types
     * @param codeIoVariables     A list of the {@link CodeIoVariable}s defined in the code
     * @param validVariables      A list of the currently defined {@link ValidFreeVariable}s
     * @param hybridSpecification The {@link HybridSpecification} to display
     */
    @SuppressWarnings("unchecked")
    public SpecificationTableController(GlobalConfig config, ObjectProperty<List<Type>> typeContext,
                                        ObjectProperty<List<CodeIoVariable>> codeIoVariables,
                                        ReadOnlyObjectProperty<List<ValidFreeVariable>> validVariables,
                                        HybridSpecification hybridSpecification) {
        this.config = config;
        this.tableView = new TableView<>();

        this.typeContext = typeContext;
        this.codeIoVariables = codeIoVariables;
        this.hybridSpec = hybridSpecification;
        this.validator = new ConstraintSpecificationValidator(typeContext, codeIoVariables,
                validVariables, hybridSpecification);
        this.durations = createViewColumn("Duration", HybridRow::getDuration);

        tableView.setColumnResizePolicy(TableView.UNCONSTRAINED_RESIZE_POLICY);

        tableView.getColumns().add(durations);

        tableView.setEditable(hybridSpecification.isEditable());
        tableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        tableView.setRowFactory(this::rowFactory);

        tableView.setContextMenu(createContextMenu());


        this.view = new SpecificationTableView(tableView);

        view.getBtnAddRows().setOnAction(event -> insertRow());
        view.getBtnCommentRow().setOnAction(event -> addRowComment());
        view.getBtnRemoveRows().setOnAction(event -> deleteRow());
        view.getBtnResize().setOnAction(event -> resizeColumns());

        //view.getHeader().setContextMenu(createTopLevelContextMenu());

        hybridSpecification.getColumnHeaders().forEach(this::addColumnToView);

        validator.problemsProperty().addListener((Observable o) -> onProblemsChange());
        validator.recalculateSpecProblems();

        hybridSpec.getSelection().setOnTimingDiagramSelectionClickListener(this::focusCell);
        hybridSpec.getSelection().columnProperty().addListener(this::onColumnSelectionChanged);

        tableView.setItems(hybridSpec.getHybridRows());
    }

    private void onColumnSelectionChanged(ObservableValue<? extends String> obs, String before,
                                          String columnNow) {
        if (before != null) {
            tableView.getColumns().stream().filter(column -> before.equals(column.getUserData()))
                    .findFirst().ifPresent(column -> {
                column.getStyleClass().remove("highlighted");
            });
        }
        if (columnNow != null) {
            // If we don't clear, the gray selection could be confused with the highlighting
            tableView.getSelectionModel().clearSelection();
            tableView.getColumns().stream().filter(column -> columnNow.equals(column.getUserData()))
                    .findFirst().ifPresent(column -> {
                column.getStyleClass().add("highlighted");
                tableView.scrollToColumn(column);
            });
        }
    }

    private void focusCell(String columnId, int row) {
        tableView.edit(row,
                tableView.getColumns().stream().filter(column -> columnId.equals(column.getUserData()))
                        .findFirst().orElseThrow(
                        () -> new IllegalArgumentException("Cannot focus unknown column: " + columnId)));
    }

    private void onProblemsChange() {
        List<ColumnProblem> columnProblems = validator.problemsProperty().get().stream()
                .filter(problem -> problem instanceof ColumnProblem).map(problem -> (ColumnProblem) problem)
                .collect(Collectors.toList());
        for (TableColumn<HybridRow, ?> column : tableView.getColumns()) {
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

    private SpecificationTableCell cellFactory(TableColumn<HybridRow, String> table) {
        return new SpecificationTableCell(validator);
    }

    private ContextMenu createTopLevelContextMenu() {
        MenuItem comment = new MenuItem("Comment ...");
        comment.setAccelerator(KeyCombination.keyCombination("Ctrl+k"));
        comment.setOnAction(event -> {
            new CommentPopupManager(hybridSpec, hybridSpec.isEditable());
        });
        return new ContextMenu(comment);
    }

    private <T> void removeByReference(List<T> toBeRemovedFrom, List<T> toRemove) {
        for (T referenceToRemove : toRemove) {
            Iterator<T> iterator = toBeRemovedFrom.iterator();
            while (iterator.hasNext()) {
                T iteratedItem = iterator.next();
                if (iteratedItem == referenceToRemove) {
                    iterator.remove();
                }
            }
        }
    }

    public void insertRow() {
        int selectedIndex = tableView.getSelectionModel().getSelectedIndex();
        addEmptyRow(selectedIndex + 1);
    }

    public void deleteRow() {
        List<HybridRow> toRemove = new ArrayList<>();
        toRemove.addAll(tableView.getSelectionModel().getSelectedItems());
        removeByReference(hybridSpec.getHybridRows(), toRemove);
    }

    public void addNewColumn() {
        new IoVariableChooserDialog(codeIoVariables, hybridSpec.getColumnHeaders())
                .showAndWait().ifPresent(this::addNewColumn);
    }

    public void addRowComment() {
        int index = tableView.getSelectionModel().getSelectedIndex();
        if (index < 0) {
            return;
        }
        CommentPopupManager popupController =
                new CommentPopupManager(hybridSpec.getRows().get(index), hybridSpec.isEditable());
    }

    public void resizeColumns() {
        LOGGER.debug("SpecificationTableController.resizeColumns");
        ViewUtils.autoFitTable(tableView);
    }


    private ContextMenu createContextMenu() {
        MenuItem insertRow = new MenuItem("Insert Row");
        MenuItem columnResize = new MenuItem("Resize columns");
        MenuItem deleteRow = new MenuItem("Delete Row");
        MenuItem comment = new MenuItem("Comment ...");

        insertRow.setAccelerator(new KeyCodeCombination(KeyCode.INSERT));
        insertRow.setOnAction(event -> insertRow());

        deleteRow.setAccelerator(new KeyCodeCombination(KeyCode.DELETE));
        deleteRow.setOnAction(event -> deleteRow());

        MenuItem addNewColumn = new MenuItem("New Column...");
        addNewColumn.setOnAction(event -> addNewColumn());

        comment.setOnAction(event -> addRowComment());
        comment.setAccelerator(KeyCodeCombination.keyCombination("Ctrl+k"));
        insertRow.disableProperty().bind(Bindings.not(tableView.editableProperty()));
        deleteRow.disableProperty().bind(Bindings.not(tableView.editableProperty()));
        addNewColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()));
        columnResize.setAccelerator(KeyCodeCombination.keyCombination("Ctrl+R"));
        columnResize.setOnAction(event -> resizeColumns());

        return new ContextMenu(insertRow, deleteRow, addNewColumn, comment, columnResize);
    }


    private ContextMenu createColumnContextMenu(TableColumn<HybridRow, ?> column) {
        MenuItem changeColumn = new MenuItem("Change Column...");
        MenuItem removeColumn = new MenuItem("Remove Column");
        MenuItem commentColumn = new MenuItem("Comment ...");
        commentColumn.setAccelerator(KeyCombination.keyCombination("Ctrl+k"));
        changeColumn.setOnAction(event -> {
            new IoVariableChangeDialog(hybridSpec.getColumnHeaderByName((String) column.getUserData()),
                    hybridSpec.getColumnHeaders()
                            .filtered(var -> !var.getName().equals(column.getUserData()))).showAndWait();
        });
        removeColumn.setOnAction(event -> {
            tableView.getColumns().remove(column);
            hybridSpec.removeColumnByName((String) column.getUserData());
        });
        commentColumn.setOnAction(event -> {
            String specIoVariableName = (String) column.getUserData();
            SpecIoVariable commentable = hybridSpec.getColumnHeaderByName(specIoVariableName);
            new CommentPopupManager(commentable, tableView.isEditable());
        });
        changeColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()));
        removeColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()));
        return new ContextMenu(changeColumn, removeColumn, commentColumn);
    }

    /**
     * Adds a new row at the specified index.
     *
     * @param index Index where the row should be added
     */
    public void addEmptyRow(int index) {
        Map<String, ConstraintCell> wildcardCells = new HashMap<>();
        hybridSpec.getColumnHeaders().forEach(
                specIoVariable -> wildcardCells.put(specIoVariable.getName(), new ConstraintCell("-")));
        SpecificationRow<ConstraintCell> wildcardRow = ConstraintSpecification.createRow(wildcardCells);
        hybridSpec.getHybridRows().add(index, new HybridRow(wildcardRow, new ConstraintDuration("1")));
    }

    /**
     * Adds a new column for the specified variable.
     *
     * @param specIoVariable variable for which the column should be added
     */
    public void addNewColumn(SpecIoVariable specIoVariable) {
        // Add column to model:
        if (hybridSpec.getHybridRows().isEmpty()) {
            hybridSpec.getColumnHeaders().add(specIoVariable);
        } else {
            SpecificationColumn<ConstraintCell> dataColumn =
                    new SpecificationColumn<>(hybridSpec.getHybridRows().stream()
                            .map(row -> new ConstraintCell("-")).collect(Collectors.toList()));
            hybridSpec.addColumn(specIoVariable, dataColumn);
        }

        // Add column to view:
        addColumnToView(specIoVariable);
    }

    private void addColumnToView(final SpecIoVariable specIoVariable) {
        TableColumn<HybridRow, String> column = createViewColumn(specIoVariable.getName(),
                hybridRow -> hybridRow.getCells().get(specIoVariable.getName()));

        column.setUserData(specIoVariable.getName());
        specIoVariable.nameProperty()
                .addListener((Observable o) -> column.setUserData(specIoVariable.getName()));
        column.setText("");
        column.setGraphic(new ColumnHeader(specIoVariable));
        column.setPrefWidth(specIoVariable.getColumnConfig().getWidth());
        column.widthProperty().addListener(
                (obs, old, newVal) -> specIoVariable.getColumnConfig().setWidth(newVal.doubleValue()));
        column.setContextMenu(createColumnContextMenu(column));

        tableView.getColumns().add(tableView.getColumns().size() - 1, column);
    }

    private TableColumn<HybridRow, String> createViewColumn(String colName,
                                                            final Function<HybridRow, HybridCell<?>> extractCellFromRow) {
        TableColumn<HybridRow, String> column = new TableColumn<>(colName);
        column.setSortable(false);
        column.setEditable(true);
        column.setPrefWidth(100);
        column.setCellFactory(this::cellFactory);

        column.setCellValueFactory(rowModelData -> extractCellFromRow.apply(rowModelData.getValue())
                .stringRepresentationProperty());

        return column;
    }

    private TableRow<HybridRow> rowFactory(TableView<HybridRow> tableView) {
        TableRow<HybridRow> row = new TableRow<HybridRow>() {
            {
                hybridSpec.getSelection().rowProperty().addListener(this::rowSelectionChanged);
            }

            private void rowSelectionChanged(ObservableValue<? extends Integer> obs, Integer before,
                                             Integer now) {
                if (before != null && getIndex() == before) {
                    getStyleClass().remove("highlighted");
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
                if (tableView.isEditable()
                        && row.getIndex() != (Integer) db.getContent(SERIALIZED_MIME_TYPE)) {
                    event.acceptTransferModes(TransferMode.COPY_OR_MOVE);
                    event.consume();
                }
            }
        });

        row.setOnDragDropped(event -> {
            Dragboard db = event.getDragboard();
            if (db.hasContent(SERIALIZED_MIME_TYPE)) {
                int draggedIndex = (Integer) db.getContent(SERIALIZED_MIME_TYPE);
                HybridRow draggedRow = tableView.getItems().remove(draggedIndex);

                int dropIndex;

                if (row.isEmpty()) {
                    dropIndex = tableView.getItems().size();
                } else {
                    dropIndex = row.getIndex();
                }

                tableView.getItems().add(dropIndex, draggedRow);

                event.setDropCompleted(true);
                tableView.getSelectionModel().clearAndSelect(dropIndex);

                //update indexProperty on TableCells (needed for the IndexColumn's CommentIcon)
                tableView.refresh();

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
