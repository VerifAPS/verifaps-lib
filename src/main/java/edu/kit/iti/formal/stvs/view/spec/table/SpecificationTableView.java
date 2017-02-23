package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.HybridRow;
import javafx.scene.control.Label;
import javafx.scene.control.TableView;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 18.02.17.
 * @author Carsten Csiky
 */
public class SpecificationTableView extends VBox {
  private Label header;
  private TableView<HybridRow> tableView;


  public SpecificationTableView(Label header, TableView<HybridRow> tableView) {
    this.getStylesheets().add(SpecificationTableController.class.getResource("style.css")
        .toExternalForm());

    this.header = header;
    header.getStyleClass().add("spec-header");
    this.tableView = tableView;
    this.getChildren().addAll(header, tableView);
  }

  public SpecificationTableView(TableView<HybridRow> tableView) {
    this(new Label("Specification-Table:"), tableView);
  }

  public Label getHeader() {
    return header;
  }

  public TableView<HybridRow> getTableView() {
    return tableView;
  }
}
