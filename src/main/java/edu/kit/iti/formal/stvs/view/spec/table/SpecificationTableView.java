package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.HybridRow;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.StageStyle;

/**
 * The view responsible for displaying
 * {@link edu.kit.iti.formal.stvs.model.table.HybridSpecification}s.
 *
 * @author Carsten Csiky
 */
public class SpecificationTableView extends VBox {
  private Label header;
  private TableView<HybridRow> tableView;


  /**
   * Create a new SpecificationTableView from a given header label and a {@link TableView} of
   * {@link HybridRow}s.
   * @param header The header of this view
   * @param tableView The underlying {@link TableView} of {@link HybridRow}s
   */
  public SpecificationTableView(Label header, TableView<HybridRow> tableView) {
    this.header = header;
    header.getStyleClass().addAll("spec-header", "header");
    this.tableView = tableView;
    tableView.getColumns().add(0, createIndexColumn());
    this.getChildren().addAll(header, tableView);
    setVgrow(tableView, Priority.ALWAYS);
    ViewUtils.setupView(this);


    header.setOnMouseClicked(event -> {
      if(event.isAltDown()) {
        System.out.println("SpecificationTableView.SpecificationTableView");
        Stage s = new Stage(StageStyle.UTILITY);
        s.initModality(Modality.APPLICATION_MODAL);
        //s.setFullScreen(true);
        s.setMaximized(true);
        //TableView<HybridRow> newView = new TableView<>(tableView.getItems());
          getChildren().remove(tableView);
        BorderPane root = new BorderPane(tableView);
        ButtonBar bb = new ButtonBar();
        root.setTop(bb);
        s.setScene(new Scene(root));
        Button yesButton = new Button("Close");
        ButtonBar.setButtonData(yesButton, ButtonBar.ButtonData.CANCEL_CLOSE);
        s.showAndWait();
          getChildren().addAll(tableView);
      }
    });
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

  /**
   * Create a new SpecificationTableView from a given {@link TableView} of {@link HybridRow}s.
   * @param tableView The underlying {@link TableView} of {@link HybridRow}s
   */
  public SpecificationTableView(TableView<HybridRow> tableView) {
    this(new Label("Specification Table:"), tableView);
  }

  public Label getHeader() {
    return header;
  }

  public TableView<HybridRow> getTableView() {
    return tableView;
  }
}
