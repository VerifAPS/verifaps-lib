package edu.kit.iti.formal.stvs.view.spec.table;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIconView;
import edu.kit.iti.formal.stvs.model.table.HybridRow;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.StageStyle;

/**
 * The view responsible for displaying
 * {@link edu.kit.iti.formal.stvs.model.table.HybridSpecification}s.
 *
 * @author Carsten Csiky
 * @author Alexander Weigl
 */
public class SpecificationTableView extends TitledPane {
    private final ToolBar toolbar = new ToolBar();
    private final VBox content = new VBox();
    private final Button btnRemoveRows = new Button("Remove Rows",
            new FontAwesomeIconView(FontAwesomeIcon.MINUS_SQUARE));
    private final Button btnAddRows = new Button("Add Row",
            new FontAwesomeIconView(FontAwesomeIcon.PLUS_SQUARE));
    private final Button btnResize = new Button("Resize",
            new FontAwesomeIconView(FontAwesomeIcon.FLAG_CHECKERED));
    private final Button btnCommentRow = new Button("Comment",
            new FontAwesomeIconView(FontAwesomeIcon.COMMENT));
    private TableView<HybridRow> tableView;


    /**
     * Create a new SpecificationTableView from a given header label and a {@link TableView} of
     * {@link HybridRow}s.
     *
     * @param tableView The underlying {@link TableView} of {@link HybridRow}s
     */
    public SpecificationTableView(TableView<HybridRow> tableView) {
        this.tableView = tableView;
        setContent(content);
        setText("Specification Table");
        content.getChildren().addAll(toolbar, tableView);
        VBox.setVgrow(tableView, Priority.ALWAYS);
        tableView.getColumns().add(0, createIndexColumn());
        ViewUtils.setupView(this);
//        setOnMouseClicked(this::showInDialog);

        Button btnOpenExternal = new Button();
        btnOpenExternal.setGraphic(new FontAwesomeIconView(FontAwesomeIcon.EXTERNAL_LINK_SQUARE));
        btnOpenExternal.setOnAction(this::showInDialog);
        setGraphic(btnOpenExternal);
        setContentDisplay(ContentDisplay.RIGHT);


        btnResize.setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
        btnCommentRow.setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
        btnAddRows.setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
        btnRemoveRows.setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
        Region stretch = new Region();
        HBox.setHgrow(stretch, Priority.ALWAYS);
        toolbar.getItems().addAll(
//                new Label("Column:"),
                stretch, btnResize, btnCommentRow, btnAddRows, btnRemoveRows
        );
    }

    private void showInDialog(javafx.event.ActionEvent event) {
        //("SpecificationTableView.SpecificationTableView");
        Stage s = new Stage(StageStyle.DECORATED);
        s.setTitle(getText());
        s.initModality(Modality.APPLICATION_MODAL);
        s.setMinHeight(640);
        s.setMinHeight(480);
        s.setFullScreen(true);
        //s.setMaximized(true);
        //TableView<HybridRow> newView = new TableView<>(tableView.getItems());
        setContent(new Label("opened externally"));
        BorderPane root = new BorderPane(tableView);
        ButtonBar bb = new ButtonBar();
        root.setTop(bb);
        s.setScene(new Scene(root));
        Button yesButton = new Button("Close");
        ButtonBar.setButtonData(yesButton, ButtonBar.ButtonData.CANCEL_CLOSE);
        bb.getButtons().addAll(yesButton);
        yesButton.setOnAction(e -> s.hide());
        s.showAndWait();
        setContent(tableView);
    }

    /**
     * creates the index column at the front of the table
     */
    private TableColumn<HybridRow, String> createIndexColumn() {
        TableColumn<HybridRow, String> indexColumn = new TableColumn<>("#");
        indexColumn.setSortable(false);
        indexColumn.setCellFactory(hybridRowObjectTableColumn ->
                new IndexTableCell(tableView)
        );
        return indexColumn;
    }

  /*public Label getHeader() {
    return header;
  }*/

    public TableView<HybridRow> getTableView() {
        return tableView;
    }

    public Button getBtnRemoveRows() {
        return btnRemoveRows;
    }

    public Button getBtnAddRows() {
        return btnAddRows;
    }

    public Button getBtnResize() {
        return btnResize;
    }

    public Button getBtnCommentRow() {
        return btnCommentRow;
    }
}
