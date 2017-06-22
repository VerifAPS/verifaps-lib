package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.HybridRow;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.scene.control.Label;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

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
    header.getStyleClass().add("spec-header");
    this.tableView = tableView;
    tableView.getColumns().add(0, createIndexColumn());
    this.getChildren().addAll(header, tableView);
    setVgrow(tableView, Priority.ALWAYS);
    ViewUtils.setupView(this);
  }

  /**
   * creates the index column at the front of the table
   */
  private TableColumn<HybridRow, Object> createIndexColumn() {
    TableColumn<HybridRow, Object> indexColumn = new TableColumn<>("#");
    indexColumn.setSortable(false);
    indexColumn.setCellFactory(hybridRowObjectTableColumn ->
      new TableCell<HybridRow, Object>(){

        @Override
        protected void updateItem(Object item, boolean empty) {
          super.updateItem(item, empty);
          if (empty) {
            setText("");
          } else {
            setText(this.getIndex() + "");
          }
        }
      }
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
