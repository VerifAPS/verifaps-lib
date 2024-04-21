package edu.kit.iti.formal.stvs.view.spec.variables

import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.layout.*
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

/**
 * This is the view that displays free variables and offers editing them.
 *
 * @author Philipp
 * @author Alexander Weigl
 */
class VariableCollection : TitledPane() {
    val freeVariableTableView: TableView<FreeVariable> = TableView()
    val nameTableColumn: TableColumn<FreeVariable, String> = TableColumn("Name")
    val typeTableColumn: TableColumn<FreeVariable, String> = TableColumn("Type")
    val constraintTableColumn: TableColumn<FreeVariable, String> = TableColumn("Constraint")

    private val content = BorderPane()
    private val toolBar = ToolBar()
    val btnRemoveRow: Button = Button(
        "Remove Rows",
        FontIcon(FontAwesomeSolid.MINUS_SQUARE)
    )
    val btnAddRow: Button = Button(
        "Add Rows",
        FontIcon(FontAwesomeSolid.PLUS_SQUARE)
    )


    //private final Button btnRemoveRow = new Button();
    /**
     * Creates an instance of this view.
     */
    init {
        text = "Global Variables"
        freeVariableTableView.id = "VariableCollectionTableView"
        ViewUtils.setupView(this)
        isExpanded = false

        nameTableColumn.prefWidthProperty().bind(freeVariableTableView.widthProperty().multiply(0.4))
        typeTableColumn.prefWidthProperty().bind(freeVariableTableView.widthProperty().multiply(0.4))
        constraintTableColumn.prefWidthProperty()
            .bind(freeVariableTableView.widthProperty().multiply(0.2))

        nameTableColumn.userData = Column.NAME
        typeTableColumn.userData = Column.TYPE
        constraintTableColumn.userData = Column.CONSTRAINT

        freeVariableTableView.isEditable = true
        freeVariableTableView.selectionModel.selectionMode = SelectionMode.MULTIPLE
        freeVariableTableView.columns.setAll(nameTableColumn, typeTableColumn, constraintTableColumn)

        val stretch = Region()
        HBox.setHgrow(stretch, Priority.ALWAYS)

        //this.overviewLabel.getStyleClass().addAll("freevar", "overview-label");
        freeVariableTableView.styleClass.addAll("freevar", "variable-table-view")
        freeVariableTableView.prefHeight = 100.0
        setContent(content)
        content.center = freeVariableTableView
        content.top = toolBar

        btnAddRow.contentDisplay = ContentDisplay.GRAPHIC_ONLY
        btnRemoveRow.contentDisplay = ContentDisplay.GRAPHIC_ONLY
        toolBar.items.setAll(stretch, btnAddRow, btnRemoveRow)
        minHeight = 0.0
        maxHeight = 1000.0
    }

    fun removeVariableView(view: Node?) {
        children.removeAll(view)
    }

    enum class Column {
        NAME, TYPE, CONSTRAINT
    }
}
