package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.*
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.table.problems.ColumnProblem
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import edu.kit.iti.formal.stvs.view.*
import javafx.beans.InvalidationListener
import javafx.beans.Observable
import javafx.beans.binding.Bindings
import javafx.beans.property.ListProperty
import javafx.beans.value.ObservableValue
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.Event
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.input.*
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.util.function.Consumer
import java.util.function.Function
import java.util.stream.Collectors

/**
 * The controller for the [SpecificationTableView]. Orchestrates complex user interactions on
 * the view (such as dragging and dropping of rows, selecting columns and cells etc.) and trigger
 * updates on the model (the underlying [HybridSpecification]).
 *
 * @author Philipp
 */
class SpecificationTableController(
    private val config: GlobalConfig, private val typeContext: ListProperty<Type>,
    private val codeIoVariables: ListProperty<CodeIoVariable>,
    validVariables: ObservableList<ValidFreeVariable>,
    val hybridSpecification: HybridSpecification?
) : Controller {
    override val view: SpecificationTableView
    private val tableView = TableView<HybridRow>()

    val validator: ConstraintSpecificationValidator = ConstraintSpecificationValidator(
        typeContext, codeIoVariables,
        validVariables, hybridSpecification!!
    )
    private val durations: TableColumn<HybridRow?, String>

    /**
     * Create a new SpecificationTableController.
     *
     * @param config              A reference to the current [GlobalConfig]
     * @param typeContext         A list of the currently defined types
     * @param codeIoVariables     A list of the [CodeIoVariable]s defined in the code
     * @param validVariables      A list of the currently defined [ValidFreeVariable]s
     * @param hybridSpecification The [HybridSpecification] to display
     */
    init {
        this.durations = createViewColumn("Duration", { it?.duration })

        tableView.columnResizePolicy = TableView.UNCONSTRAINED_RESIZE_POLICY

        tableView.columns.add(durations)

        tableView.isEditable = hybridSpecification!!.isEditable
        tableView.selectionModel.selectionMode = SelectionMode.MULTIPLE
        tableView.setRowFactory { tableView: TableView<HybridRow?> -> this.rowFactory(tableView) }

        tableView.contextMenu = createContextMenu()


        this.view = SpecificationTableView(tableView)

        view.btnAddRows.onAction = EventHandler { event: ActionEvent? -> insertRow() }
        view.btnCommentRow.onAction = EventHandler { event: ActionEvent? -> addRowComment(event) }
        view.btnRemoveRows.onAction = EventHandler { event: ActionEvent? -> deleteRow() }
        view.btnResize.onAction = EventHandler { event: ActionEvent? -> resizeColumns() }

        //view.getHeader().setContextMenu(createTopLevelContextMenu());
        hybridSpecification.columnHeaders
            .forEach(Consumer { specIoVariable: SpecIoVariable -> this.addColumnToView(specIoVariable) })

        validator.problemsProperty().addListener { o: Observable? -> onProblemsChange() }
        validator.recalculateSpecProblems()

        hybridSpecification.getSelection()
            .setOnTimingDiagramSelectionClickListener({ columnId: String?, row: Int? ->
                this.focusCell(columnId, row!!)
            })

        hybridSpecification.getSelection()
            .columnProperty().addListener { obs, before: String?, columnNow: String? ->
                this.onColumnSelectionChanged(obs, before, columnNow)
            }

        tableView.setItems(hybridSpecification.hybridRows)
    }

    private fun onColumnSelectionChanged(
        obs: ObservableValue<out String?>, before: String?,
        columnNow: String?
    ) {
        if (before != null) {
            tableView.columns.stream().filter { column: TableColumn<HybridRow?, *> -> before == column.userData }
                .findFirst().ifPresent { column: TableColumn<HybridRow?, *> ->
                    column.styleClass.remove("highlighted")
                }
        }
        if (columnNow != null) {
            // If we don't clear, the gray selection could be confused with the highlighting
            tableView.selectionModel.clearSelection()
            tableView.columns.stream().filter { column: TableColumn<HybridRow?, *> -> columnNow == column.userData }
                .findFirst().ifPresent { column: TableColumn<HybridRow?, *> ->
                    column.styleClass.add("highlighted")
                    tableView.scrollToColumn(column)
                }
        }
    }

    private fun focusCell(columnId: String?, row: Int) {
        tableView.edit(row,
            tableView.columns.stream().filter { column: TableColumn<HybridRow?, *> -> columnId == column.userData }
                .findFirst().orElseThrow { IllegalArgumentException("Cannot focus unknown column: $columnId") })
    }

    private fun onProblemsChange() {
        val columnProblems = validator.problemsProperty().get()
            .filterIsInstance<ColumnProblem>()
        for (column in tableView.columns) {
            if (column.userData == null) {
                continue
            }
            val problemsForColumn = columnProblems.stream()
                .filter { problem: ColumnProblem -> problem.column == column.userData }
                .collect(Collectors.toList())

            val columnHeader = column.graphic as ColumnHeader

            if (problemsForColumn.isEmpty()) {
                columnHeader.resetProblems()
            } else {
                columnHeader.configureProblems(problemsForColumn)
            }
        }
    }

    private fun cellFactory(table: TableColumn<HybridRow?, String>): SpecificationTableCell {
        return SpecificationTableCell(validator)
    }

    private fun <T> removeByReference(toBeRemovedFrom: MutableList<T>?, toRemove: List<T>) {
        for (referenceToRemove in toRemove) {
            val iterator = toBeRemovedFrom!!.iterator()
            while (iterator.hasNext()) {
                val iteratedItem = iterator.next()
                if (iteratedItem === referenceToRemove) {
                    iterator.remove()
                }
            }
        }
    }

    fun insertRow() {
        val selectedIndex = tableView.selectionModel.selectedIndex
        addEmptyRow(selectedIndex + 1)
    }

    fun deleteRow() {
        val toRemove: MutableList<HybridRow?> = ArrayList()
        toRemove.addAll(tableView.selectionModel.selectedItems)
        removeByReference(hybridSpecification!!.hybridRows, toRemove)
    }

    fun addNewColumn() {
        IoVariableChooserDialog(codeIoVariables, hybridSpecification!!.columnHeaders)
            .showAndWait().ifPresent { specIoVariable: SpecIoVariable -> this.addNewColumn(specIoVariable) }
    }

    fun addRowComment(event: Event?) {
        val index = tableView.selectionModel.selectedIndex
        if (index < 0) {
            return
        }
        val tableColumn = tableView.columns[1]
        val popOverManager =
            CommentPopOverManager(
                hybridSpecification!!.rows[index],
                hybridSpecification.isEditable,
                tableColumn.graphic,
                0.0,
                200.0
            )
    }

    fun resizeColumns() {
        LOGGER.debug("SpecificationTableController.resizeColumns")
        ViewUtils.autoFitTable(tableView)
    }


    private fun createContextMenu(): ContextMenu {
        val insertRow = MenuItem("Insert Row")
        val columnResize = MenuItem("Resize columns")
        val deleteRow = MenuItem("Delete Row")
        val comment = MenuItem("Comment ...")

        insertRow.accelerator = KeyCodeCombination(KeyCode.INSERT)
        insertRow.onAction = EventHandler { event: ActionEvent? -> insertRow() }

        deleteRow.accelerator = KeyCodeCombination(KeyCode.DELETE)
        deleteRow.onAction = EventHandler { event: ActionEvent? -> deleteRow() }

        val addNewColumn = MenuItem("New Column...")
        addNewColumn.onAction = EventHandler { event: ActionEvent? -> addNewColumn() }

        comment.onAction = EventHandler { event: ActionEvent? -> addRowComment(event) }
        comment.accelerator = KeyCodeCombination.keyCombination("Ctrl+k")
        insertRow.disableProperty().bind(Bindings.not(tableView.editableProperty()))
        deleteRow.disableProperty().bind(Bindings.not(tableView.editableProperty()))
        addNewColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()))
        columnResize.accelerator = KeyCodeCombination.keyCombination("Ctrl+R")
        columnResize.onAction = EventHandler { event: ActionEvent? -> resizeColumns() }

        return ContextMenu(insertRow, deleteRow, addNewColumn, comment, columnResize)
    }


    private fun createColumnContextMenu(column: TableColumn<HybridRow?, *>): ContextMenu {
        val changeColumn = MenuItem("Change Column...")
        val removeColumn = MenuItem("Remove Column")
        val commentColumn = MenuItem("Comment ...")
        commentColumn.accelerator = KeyCombination.keyCombination("Ctrl+k")
        changeColumn.onAction = EventHandler { event: ActionEvent? ->
            IoVariableChangeDialog(
                hybridSpecification!!.getColumnHeaderByName(column.userData as String),
                hybridSpecification.columnHeaders
                    .filtered({ `var`: SpecIoVariable -> !`var`.name.equals(column.userData) })
            ).showAndWait()
        }
        removeColumn.onAction = EventHandler { event: ActionEvent? ->
            tableView.columns.remove(column)
            hybridSpecification!!.removeColumnByName(column.userData as String)
        }
        commentColumn.onAction = EventHandler { event: ActionEvent? ->
            val specIoVariableName = column.userData as String
            val commentable = hybridSpecification!!.getColumnHeaderByName(specIoVariableName)
            CommentPopOverManager(commentable, tableView.isEditable, column.graphic)
        }
        changeColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()))
        removeColumn.disableProperty().bind(Bindings.not(tableView.editableProperty()))
        return ContextMenu(changeColumn, removeColumn, commentColumn)
    }

    /**
     * Adds a new row at the specified index.
     *
     * @param index Index where the row should be added
     */
    fun addEmptyRow(index: Int) {
        val wildcardCells: MutableMap<String, ConstraintCell> = HashMap()
        hybridSpecification!!.columnHeaders.forEach(
            Consumer { specIoVariable: SpecIoVariable ->
                wildcardCells[specIoVariable.name] = ConstraintCell("-")
            })
        val wildcardRow = ConstraintSpecification.createRow(wildcardCells)
        hybridSpecification.hybridRows.add(index, HybridRow(wildcardRow, ConstraintDuration("1")))
    }

    /**
     * Adds a new column for the specified variable.
     *
     * @param specIoVariable variable for which the column should be added
     */
    fun addNewColumn(specIoVariable: SpecIoVariable) {
        // Add column to model:
        if (hybridSpecification!!.hybridRows.isEmpty()) {
            hybridSpecification.columnHeaders.add(specIoVariable)
        } else {
            val dataColumn =
                SpecificationColumn(
                    hybridSpecification.hybridRows.stream()
                        .map<ConstraintCell>({ row: HybridRow? -> ConstraintCell("-") })
                        .collect(Collectors.toList())
                )
            hybridSpecification.addColumn(specIoVariable, dataColumn)
        }

        // Add column to view:
        addColumnToView(specIoVariable)
    }

    private fun addColumnToView(specIoVariable: SpecIoVariable) {
        val column = createViewColumn(
            specIoVariable.name
        ) { hybridRow: HybridRow? -> hybridRow!!.cells[specIoVariable.name] }

        column.userData = specIoVariable.name
        specIoVariable.nameProperty
            .addListener(InvalidationListener { o: Observable? -> column.setUserData(specIoVariable.name) })
        column.text = ""
        column.graphic = ColumnHeader(specIoVariable)
        column.prefWidth = specIoVariable.columnConfig.width
        column.widthProperty().addListener { obs: ObservableValue<out Number>?, old: Number?, newVal: Number ->
            specIoVariable.columnConfig.width = newVal.toDouble()
        }
        column.contextMenu = createColumnContextMenu(column)

        tableView.columns.add(tableView.columns.size - 1, column)
    }

    private fun createViewColumn(
        colName: String?,
        extractCellFromRow: Function<HybridRow?, HybridCell<*>?>
    ): TableColumn<HybridRow?, String> {
        val column = TableColumn<HybridRow?, String>(colName)
        column.isSortable = false
        column.isEditable = true
        column.prefWidth = 100.0
        column.setCellFactory { table: TableColumn<HybridRow?, String> -> this.cellFactory(table) }

        column.setCellValueFactory {
            extractCellFromRow.apply(it.value)?.stringRepresentationProperty
        }

        return column
    }

    private fun rowFactory(tableView: TableView<HybridRow?>): TableRow<HybridRow?> {
        val row: TableRow<HybridRow?> = object : TableRow<HybridRow?>() {
            init {
                hybridSpecification!!.getSelection()
                    .rowProperty().addListener { obs, before: Int?, now: Int? ->
                        this.rowSelectionChanged(before, now)
                    }
            }

            private fun rowSelectionChanged(before: Int?, now: Int?) {
                if (before != null && index == before) {
                    styleClass.remove("highlighted")
                }
                if (now != null && index == now) {
                    styleClass.add("highlighted")
                    tableView.scrollTo(index)
                }
            }
        }

        row.onDragDetected = EventHandler { event: MouseEvent ->
            if (!row.isEmpty) {
                val index = row.index
                tableView.selectionModel.clearAndSelect(index)
                val db = row.startDragAndDrop(TransferMode.MOVE)
                db.dragView = row.snapshot(null, null)
                val cc = ClipboardContent()
                cc[SERIALIZED_MIME_TYPE] = index
                db.setContent(cc)
                event.consume()
            }
        }

        row.onDragOver = EventHandler { event: DragEvent ->
            val db = event.dragboard
            if (db.hasContent(SERIALIZED_MIME_TYPE)) {
                if (tableView.isEditable
                    && row.index != db.getContent(SERIALIZED_MIME_TYPE) as Int
                ) {
                    event.acceptTransferModes(*TransferMode.COPY_OR_MOVE)
                    event.consume()
                }
            }
        }

        row.onDragDropped = EventHandler { event: DragEvent ->
            val db = event.dragboard
            if (db.hasContent(SERIALIZED_MIME_TYPE)) {
                val draggedIndex = db.getContent(SERIALIZED_MIME_TYPE) as Int
                val draggedRow = tableView.items.removeAt(draggedIndex)

                val dropIndex = if (row.isEmpty) {
                    tableView.items.size
                } else {
                    row.index
                }

                tableView.items.add(dropIndex, draggedRow)

                event.isDropCompleted = true
                tableView.selectionModel.clearAndSelect(dropIndex)

                //update indexProperty on TableCells (needed for the IndexColumn's CommentIcon)
                tableView.refresh()

                event.consume()
            }
        }

        return row
    }

    companion object {
        val LOGGER: Logger = LoggerFactory.getLogger(SpecificationTableController::class.java)

        private val SERIALIZED_MIME_TYPE = DataFormat("application/x-java-serialized-object")
    }
}
