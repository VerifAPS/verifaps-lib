package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.scene.control.Label;
import javafx.scene.control.TableView;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 18.02.17.
 * @author Carsten Csiky
 */
public class SpecificationTableView extends VBox {
  private Label header;
  private TableView<SynchronizedRow> tableView;


  public SpecificationTableView(Label header, TableView<SynchronizedRow> tableView) {
    this.getStylesheets().add(SpecificationTableController.class.getResource("style.css")
        .toExternalForm());

    this.header = header;
    header.getStyleClass().add("spec-header");
    this.tableView = tableView;
    this.getChildren().addAll(header, tableView);
  }

  public SpecificationTableView(TableView<SynchronizedRow> tableView) {
    this(new Label("Specification-Table:"), tableView);
  }

  public Label getHeader() {
    return header;
  }

  public TableView<SynchronizedRow> getTableView() {
    return tableView;
  }
}
