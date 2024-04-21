package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.table.HybridRow
import javafx.beans.property.*
import javafx.beans.value.ChangeListener
import javafx.beans.value.ObservableValue
import javafx.scene.control.*
import javafx.scene.text.Text
import javafx.scene.text.TextAlignment
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

/**
 * Created by csicar on 22.06.17.
 * IndexTableCell displays the index of the current row in a cell.
 */
class IndexTableCell(private val tableView: TableView<*>?) : TableCell<HybridRow?, String?>() {
    private val icon: Text = FontIcon(FontAwesomeRegular.FILE_CODE)
    private val tooltip = Tooltip()

    /**
     * IndexTableCell
     * @param tableView the table the index-cell should be attached to. This value is required for
     * displaying the comment icon.
     */
    init {
        val indexChangeListener =
            ChangeListener { observableValue: ObservableValue<out Number>?, oldIndex: Number?, newIndexNumber: Number ->
                val newIndex = newIndexNumber.toInt()
                if (newIndex < 0) {
                    return@ChangeListener
                }
                icon.visibleProperty().bind(getCommentPropertyByIndex(newIndex)!!.isEmpty().not())
                tooltip.textProperty().bind(getCommentPropertyByIndex(newIndex))
            }
        indexChangeListener.changed(null, 0, this.index)
        indexProperty().addListener(indexChangeListener)

        this.graphic = icon
        this.textAlignment = TextAlignment.RIGHT
        this.setTooltip(tooltip)
    }

    private fun getCommentPropertyByIndex(index: Int): StringProperty {
        if (tableView == null || index < 0 || index >= tableView.items.size) {
            return SimpleStringProperty("")
        }
        return (tableView.items[index] as HybridRow).commentProperty
    }

    override fun updateItem(item: String?, empty: Boolean) {
        super.updateItem(item, empty)
        val value = if (empty) {
            ""
        } else {
            index.toString() + ""
        }
        text = value + ""
    }
}
