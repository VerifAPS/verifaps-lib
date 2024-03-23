package edu.kit.iti.formal.stvs.view.spec.table;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.model.table.HybridRow;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ChangeListener;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableView;
import javafx.scene.control.Tooltip;
import javafx.scene.text.Text;
import javafx.scene.text.TextAlignment;


/**
 * Created by csicar on 22.06.17.
 * IndexTableCell displays the index of the current row in a cell.
 */
public class IndexTableCell extends TableCell<HybridRow, String> {
  private TableView tableView;
  private final Text icon = GlyphsDude.createIcon(FontAwesomeIcon.FILE_TEXT);
  private final Tooltip tooltip = new Tooltip();

  /**
   * IndexTableCell
   * @param tableView the table the index-cell should be attached to. This value is required for
   *                  displaying the comment icon.
   */
  public IndexTableCell(TableView tableView) {
    super();
    this.tableView = tableView;
    ChangeListener<Number> indexChangeListener = (observableValue, oldIndex, newIndexNumber) -> {
      int newIndex = newIndexNumber.intValue();
      if (newIndex < 0) {
        return;
      }
      icon.visibleProperty().bind(getCommentPropertyByIndex(newIndex).isEmpty().not());
      tooltip.textProperty().bind(getCommentPropertyByIndex(newIndex));
    };
    indexChangeListener.changed(null, 0, this.getIndex());
    this.indexProperty().addListener(indexChangeListener);

    this.setGraphic(icon);
    this.setTextAlignment(TextAlignment.RIGHT);
    this.setTooltip(tooltip);
  }

  private StringProperty getCommentPropertyByIndex(int index) {
    if (tableView == null || index < 0 || index >= tableView.getItems().size()) {
      return new SimpleStringProperty("");
    }
    return ((HybridRow) tableView.getItems().get(index)).commentProperty();
  }

  @Override
  protected void updateItem(String item, boolean empty) {
    super.updateItem(item, empty);
    final String value;
    if (empty) {
      value = "";
    } else {
      value = this.getIndex() + "";
    }
    setText(value + "");
  }
}
