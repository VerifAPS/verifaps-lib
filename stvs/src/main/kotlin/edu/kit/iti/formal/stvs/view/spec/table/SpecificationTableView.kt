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
package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.table.HybridRow
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.Scene
import javafx.scene.control.*
import javafx.scene.layout.*
import javafx.stage.Modality
import javafx.stage.Stage
import javafx.stage.StageStyle
import javafx.util.Callback
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

/**
 * The view responsible for displaying
 * [edu.kit.iti.formal.stvs.model.table.HybridSpecification]s.
 *
 * @author Carsten Csiky
 * @author Alexander Weigl
 */
class SpecificationTableView(val tableView: TableView<HybridRow>) : TitledPane() {
    private val toolbar = ToolBar()
    private val root = VBox()

    val btnRemoveRows: Button = Button(
        "Remove Rows",
        FontIcon(FontAwesomeSolid.MINUS_SQUARE),
    )
    val btnAddRows: Button = Button(
        "Add Row",
        FontIcon(FontAwesomeSolid.PLUS_SQUARE),
    )
    val btnResize: Button = Button(
        "Resize",
        FontIcon(FontAwesomeSolid.ADJUST),
    )
    val btnCommentRow: Button = Button(
        "Comment",
        FontIcon(FontAwesomeSolid.COMMENT),
    )

    /**
     * Create a new SpecificationTableView from a given header label and a [TableView] of
     * [HybridRow]s.
     *
     * @param tableView The underlying [TableView] of [HybridRow]s
     */
    init {
        content = root
        text = "Specification Table"
        root.children.addAll(toolbar, tableView)
        VBox.setVgrow(tableView, Priority.ALWAYS)
        tableView.columns.add(0, createIndexColumn())
        ViewUtils.setupView(this)

        //        setOnMouseClicked(this::showInDialog);
        val btnOpenExternal = Button()
        btnOpenExternal.graphic = FontIcon(FontAwesomeSolid.EXTERNAL_LINK_ALT)
        btnOpenExternal.onAction = EventHandler { event: ActionEvent -> this.showInDialog(event) }
        graphic = btnOpenExternal
        contentDisplay = ContentDisplay.RIGHT

        btnResize.contentDisplay = ContentDisplay.GRAPHIC_ONLY
        btnCommentRow.contentDisplay = ContentDisplay.GRAPHIC_ONLY
        btnAddRows.contentDisplay = ContentDisplay.GRAPHIC_ONLY
        btnRemoveRows.contentDisplay = ContentDisplay.GRAPHIC_ONLY
        val stretch = Region()
        HBox.setHgrow(stretch, Priority.ALWAYS)
        toolbar.items.addAll( //                new Label("Column:"),
            stretch,
            btnResize,
            btnCommentRow,
            btnAddRows,
            btnRemoveRows,
        )
    }

    private fun showInDialog(event: ActionEvent) {
        // ("SpecificationTableView.SpecificationTableView");
        val s = Stage(StageStyle.DECORATED)
        s.title = text
        s.initModality(Modality.APPLICATION_MODAL)
        s.minHeight = 640.0
        s.minHeight = 480.0
        s.isFullScreen = true
        // s.setMaximized(true);
        // TableView<HybridRow> newView = new TableView<>(tableView.getItems());
        content = Label("opened externally")
        val root = BorderPane(tableView)
        val bb = ButtonBar()
        root.top = bb
        s.scene = Scene(root)
        val yesButton = Button("Close")
        ButtonBar.setButtonData(yesButton, ButtonBar.ButtonData.CANCEL_CLOSE)
        bb.buttons.addAll(yesButton)
        yesButton.onAction = EventHandler { e: ActionEvent? -> s.hide() }
        s.showAndWait()
        content = tableView
    }

    /**
     * creates the index column at the front of the table
     */
    private fun createIndexColumn(): TableColumn<HybridRow?, String> {
        val indexColumn = TableColumn<HybridRow?, String>("#")
        indexColumn.isSortable = false
        indexColumn.cellFactory = Callback { hybridRowObjectTableColumn: TableColumn<HybridRow?, String>? ->
            IndexTableCell(
                tableView,
            )
        }
        return indexColumn
    }
}