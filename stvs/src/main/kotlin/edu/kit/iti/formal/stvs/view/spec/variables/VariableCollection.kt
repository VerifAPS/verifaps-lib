/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.view.spec.variables

import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.layout.BorderPane
import javafx.scene.layout.HBox
import javafx.scene.layout.Priority
import javafx.scene.layout.Region
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

    private val root = BorderPane()
    private val toolBar = ToolBar()
    val btnRemoveRow: Button = Button(
        "Remove Rows",
        FontIcon(FontAwesomeSolid.MINUS_SQUARE),
    )
    val btnAddRow: Button = Button(
        "Add Rows",
        FontIcon(FontAwesomeSolid.PLUS_SQUARE),
    )

    // private final Button btnRemoveRow = new Button();

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

        // this.overviewLabel.getStyleClass().addAll("freevar", "overview-label");
        freeVariableTableView.styleClass.addAll("freevar", "variable-table-view")
        freeVariableTableView.prefHeight = 100.0
        content = root
        root.center = freeVariableTableView
        root.top = toolBar

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
        NAME,
        TYPE,
        CONSTRAINT,
    }
}