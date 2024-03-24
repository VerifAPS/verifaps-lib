package edu.kit.iti.formal.stvs.view.spec.variables

import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.common.FreeVariableProblem
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.view.*
import edu.kit.iti.formal.stvs.view.spec.variables.clipboard.Json
import javafx.beans.Observable
import javafx.beans.property.ListProperty
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.control.cell.TextFieldTableCell
import javafx.scene.input.*
import javafx.util.Callback
import javafx.util.converter.DefaultStringConverter
import java.util.*
import java.util.stream.Collectors
import kotlin.math.min

/**
 * This is a controller for [VariableCollection].
 *
 * @author Philipp
 */
class VariableCollectionController(
    codeTypes: ListProperty<Type>,
    val freeVariableList: FreeVariableList?
) : Controller {
    val validator: FreeVariableListValidator = FreeVariableListValidator(codeTypes, freeVariableList!!)
    override val view: VariableCollection = VariableCollection()

    private var contextMenu = ContextMenu()

    /**
     * Creates an instance with a predefined list of variables.
     * The available types in code must be known for validation purposes.
     *
     * @param codeTypes        Available code types
     * @param freeVariableList Predefined free variables
     */
    init {
        /* Set up context menu */
        this.contextMenu = ContextMenu()

        val menuItemAdd = MenuItem("Add Variable")
        menuItemAdd.onAction = EventHandler { actionEvent: ActionEvent -> this.onAddVariableClicked(actionEvent) }
        menuItemAdd.accelerator = KeyCodeCombination(KeyCode.ADD)
        contextMenu.items.add(menuItemAdd)

        val menuItemDelete = MenuItem("Delete Variable")
        menuItemDelete.onAction = EventHandler { actionEvent: ActionEvent -> this.onDeleteVariableClicked(actionEvent) }
        menuItemDelete.accelerator = KeyCodeCombination(KeyCode.DELETE)
        contextMenu.items.add(menuItemDelete)

        view.freeVariableTableView.contextMenu = contextMenu
        view.freeVariableTableView.rowFactory =
            Callback { tableView: TableView<FreeVariable?> -> this.rowFactory(tableView) }

        view.nameTableColumn.cellValueFactory = Callback { it.value?.nameProperty }
        view.typeTableColumn.cellValueFactory = Callback { it.value?.typeProperty }
        view.constraintTableColumn.cellValueFactory = Callback { it.value?.constraintProperty }

        view.nameTableColumn.cellFactory =
            Callback { tableColumn: TableColumn<FreeVariable?, String?> -> this.cellFactory(tableColumn) }
        view.typeTableColumn.cellFactory =
            Callback { tableColumn: TableColumn<FreeVariable?, String?> -> this.cellFactory(tableColumn) }
        view.constraintTableColumn.cellFactory =
            Callback { tableColumn: TableColumn<FreeVariable?, String?> -> this.cellFactory(tableColumn) }

        view.freeVariableTableView.items = freeVariableList!!.variables


        view.btnAddRow.onAction = EventHandler { actionEvent: ActionEvent -> this.onAddVariableClicked(actionEvent) }
        view.btnRemoveRow.onAction =
            EventHandler { actionEvent: ActionEvent -> this.onDeleteVariableClicked(actionEvent) }
    }

    private fun onDeleteVariableClicked(actionEvent: ActionEvent) {
        val tableView = view.freeVariableTableView
        val newList: MutableList<FreeVariable?> = LinkedList()
        val sm = tableView.selectionModel.selectedIndices
        for (i in tableView.items.indices) {
            if (!sm.contains(i)) {
                newList.add(tableView.items[i])
            }
        }
        tableView.items.setAll(newList)

        // naive implementation does not work, if two rows are equals (in name, type and constraint)
        //tableView.getItems().removeAll(tableView.getSelectionModel().getSelectedItems());
        tableView.selectionModel.clearSelection()
    }

    private fun onAddVariableClicked(actionEvent: ActionEvent) {
        freeVariableList!!.variables.add(FreeVariable("variable", "BOOL"))
    }

    private fun cellFactory(
        tableColumn: TableColumn<FreeVariable?, String?>
    ): TableCell<FreeVariable?, String?> {
        return object : TextFieldTableCell<FreeVariable?, String>(DefaultStringConverter()) {
            init {
                validator.problemsProperty.addListener { o: Observable? -> onProblemsChanged() }
                styleClass.add("freevar")
                onProblemsChanged()
            }

            private fun configureProblematic(tooltip: String) {
                styleClass.remove("freevar-problem")
                styleClass.add("freevar-problem")
                setTooltip(Tooltip(tooltip))
            }

            private fun configureUnproblematic() {
                styleClass.remove("freevar-problem")
                tooltip = null
            }

            override fun updateItem(item: String, empty: Boolean) {
                super.updateItem(item, empty)
                onProblemsChanged()
            }

            private fun onProblemsChanged() {
                if (!isEmpty) {
                    val problems = validator.problemsProperty.get()
                        .getOrDefault(tableRow.item, emptyList())
                    if (problems.isEmpty()) {
                        configureUnproblematic()
                    } else {
                        configureProblematic(
                            java.lang.String.join(
                                "\n\n", problems.stream()
                                    .map(FreeVariableProblem::guiMessage).collect(Collectors.toList())
                            )
                        )
                    }
                }
            }
        }
    }

    private fun rowFactory(tableView: TableView<FreeVariable?>): TableRow<FreeVariable?> {
        val row = TableRow<FreeVariable?>()

        row.onDragDetected = EventHandler { event: MouseEvent ->
            val selected = tableView.selectionModel.selectedItems.filterNotNull()
            if (selected.isNotEmpty()) {
                val serializedSelection = Json.stringFromRealFreeVariables(selected)
                val db = tableView.startDragAndDrop(TransferMode.MOVE)
                val cc = ClipboardContent()
                cc.putString(serializedSelection)
                cc[JSON_MIME_TYPE] = serializedSelection
                db.setContent(cc)

                event.consume()
            }
        }

        row.onDragOver = EventHandler { event: DragEvent ->
            val db = event.dragboard
            if (db.hasContent(JSON_MIME_TYPE)) {
                event.acceptTransferModes(*TransferMode.COPY_OR_MOVE)
                event.consume()
            }
        }

        row.onDragDropped = EventHandler { event: DragEvent ->
            val db = event.dragboard
            if (db.hasContent(JSON_MIME_TYPE)) {
                val dragboardContent = db.getContent(JSON_MIME_TYPE).toString()
                val droppedVariables = Json.stringToRealFreeVariables(dragboardContent)

                tableView.items.removeIf { freeVariable: FreeVariable? ->
                    droppedVariables.any { v: FreeVariable? -> v!!.name == freeVariable!!.name }
                }

                val dropIndex = row.index
                tableView.items.addAll(
                    min(dropIndex, tableView.items.size),
                    droppedVariables
                )

                tableView.selectionModel.clearSelection()
                tableView.selectionModel.selectRange(dropIndex, dropIndex + droppedVariables.size)

                event.isDropCompleted = true
                event.consume()
            }
        }
        return row
    }

    companion object {
        private val JSON_MIME_TYPE = DataFormat("application/json")
    }
}
