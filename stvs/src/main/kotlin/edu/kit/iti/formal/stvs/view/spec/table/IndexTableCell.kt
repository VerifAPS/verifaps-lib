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
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import javafx.beans.value.ChangeListener
import javafx.beans.value.ObservableValue
import javafx.scene.control.TableCell
import javafx.scene.control.TableView
import javafx.scene.control.Tooltip
import javafx.scene.text.Text
import javafx.scene.text.TextAlignment
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular
import org.kordamp.ikonli.javafx.FontIcon

/**
 * Created by csicar on 22.06.17.
 * IndexTableCell displays the index of the current row in a cell.
 */
class IndexTableCell(private val tableView: TableView<*>?) : TableCell<HybridRow?, String?>() {
    private val icon: Text = FontIcon(FontAwesomeRegular.FILE_CODE)

    /**
     * IndexTableCell
     * @param tableView the table the index-cell should be attached to. This value is required for
     * displaying the comment icon.
     */
    init {
        tooltip = Tooltip("")

        val indexChangeListener =
            ChangeListener { observableValue: ObservableValue<out Number>?, oldIndex: Number?, newIndexNumber: Number ->
                val newIndex = newIndexNumber.toInt()
                if (newIndex < 0) {
                    return@ChangeListener
                }
                icon.visibleProperty().bind(getCommentPropertyByIndex(newIndex).isEmpty().not())
                tooltip.textProperty().bind(getCommentPropertyByIndex(newIndex))
            }
        indexChangeListener.changed(null, 0, this.index)
        indexProperty().addListener(indexChangeListener)

        this.graphic = icon
        this.textAlignment = TextAlignment.RIGHT
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