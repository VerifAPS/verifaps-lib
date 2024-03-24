package edu.kit.iti.formal.stvs.view.spec.table

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIconView
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

/**
 * The view responsible for displaying
 * [edu.kit.iti.formal.stvs.model.table.HybridSpecification]s.
 *
 * @author Carsten Csiky
 * @author Alexander Weigl
 */
class SpecificationTableView(/*public Label getHeader() {
     return header;
   }*/val tableView: TableView<HybridRow>
) : TitledPane() {
    private val toolbar = ToolBar()
    private val content = VBox()
    val btnRemoveRows: Button = Button(
        "Remove Rows",
        FontAwesomeIconView(FontAwesomeIcon.MINUS_SQUARE)
    )
    val btnAddRows: Button = Button(
        "Add Row",
        FontAwesomeIconView(FontAwesomeIcon.PLUS_SQUARE)
    )
    val btnResize: Button = Button(
        "Resize",
        FontAwesomeIconView(FontAwesomeIcon.ADJUST)
    )
    val btnCommentRow: Button = Button(
        "Comment",
        FontAwesomeIconView(FontAwesomeIcon.COMMENT)
    )


    /**
     * Create a new SpecificationTableView from a given header label and a [TableView] of
     * [HybridRow]s.
     *
     * @param tableView The underlying [TableView] of [HybridRow]s
     */
    init {
        setContent(content)
        text = "Specification Table"
        content.children.addAll(toolbar, tableView)
        VBox.setVgrow(tableView, Priority.ALWAYS)
        tableView.columns.add(0, createIndexColumn())
        ViewUtils.setupView(this)

        //        setOnMouseClicked(this::showInDialog);
        val btnOpenExternal = Button()
        btnOpenExternal.graphic = FontAwesomeIconView(FontAwesomeIcon.EXTERNAL_LINK_SQUARE)
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
            stretch, btnResize, btnCommentRow, btnAddRows, btnRemoveRows
        )
    }

    private fun showInDialog(event: ActionEvent) {
        //("SpecificationTableView.SpecificationTableView");
        val s = Stage(StageStyle.DECORATED)
        s.title = text
        s.initModality(Modality.APPLICATION_MODAL)
        s.minHeight = 640.0
        s.minHeight = 480.0
        s.isFullScreen = true
        //s.setMaximized(true);
        //TableView<HybridRow> newView = new TableView<>(tableView.getItems());
        setContent(Label("opened externally"))
        val root = BorderPane(tableView)
        val bb = ButtonBar()
        root.top = bb
        s.scene = Scene(root)
        val yesButton = Button("Close")
        ButtonBar.setButtonData(yesButton, ButtonBar.ButtonData.CANCEL_CLOSE)
        bb.buttons.addAll(yesButton)
        yesButton.onAction = EventHandler { e: ActionEvent? -> s.hide() }
        s.showAndWait()
        setContent(tableView)
    }

    /**
     * creates the index column at the front of the table
     */
    private fun createIndexColumn(): TableColumn<HybridRow?, String> {
        val indexColumn = TableColumn<HybridRow?, String>("#")
        indexColumn.isSortable = false
        indexColumn.cellFactory = Callback { hybridRowObjectTableColumn: TableColumn<HybridRow?, String>? ->
            IndexTableCell(
                tableView
            )
        }
        return indexColumn
    }
}
