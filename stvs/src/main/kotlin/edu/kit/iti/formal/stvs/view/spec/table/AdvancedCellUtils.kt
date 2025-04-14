package edu.kit.iti.formal.stvs.view.spec.table

import javafx.beans.property.ObjectProperty
import javafx.beans.value.ObservableValue
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.input.KeyCode
import javafx.scene.input.KeyEvent
import javafx.scene.layout.HBox
import javafx.util.StringConverter

/**
 * Created by Lukas on 13.07.2017.
 */
object AdvancedCellUtils {
    var TREE_VIEW_HBOX_GRAPHIC_PADDING: Int = 3

    /***************************************************************************
     * *
     * Private fields                                                          *
     * *
     */
    private val defaultStringConverter: StringConverter<*> = object : StringConverter<Any>() {
        override fun toString(t: Any): String {
            return t.toString()
        }

        override fun fromString(string: String): Any {
            return string
        }
    }

    private val defaultTreeItemStringConverter: StringConverter<*> = object : StringConverter<TreeItem<*>?>() {
        override fun toString(treeItem: TreeItem<*>?): String {
            return if ((treeItem == null || treeItem.value == null)) "" else treeItem.value.toString()
        }

        override fun fromString(string: String): TreeItem<*>? {
            return TreeItem(string)
        }
    }

    /***************************************************************************
     * *
     * General convenience                                                     *
     * *
     */
    /*
     * Simple method to provide a StringConverter implementation in various cell
     * implementations.
     */
    fun <T> defaultStringConverter(): StringConverter<T> {
        return defaultStringConverter as StringConverter<T>
    }

    /*
     * Simple method to provide a TreeItem-specific StringConverter
     * implementation in various cell implementations.
     */
    fun <T> defaultTreeItemStringConverter(): StringConverter<TreeItem<T>> {
        return defaultTreeItemStringConverter as StringConverter<TreeItem<T>>
    }

    private fun <T> getItemText(cell: Cell<T>, converter: StringConverter<T>?): String {
        return if (converter == null) if (cell.item == null) "" else cell.item.toString() else converter.toString(cell.item)
    }


    fun getGraphic(treeItem: TreeItem<*>?): Node? {
        return treeItem?.graphic
    }


    /***************************************************************************
     * *
     * ChoiceBox convenience                                                   *
     * *
     */
    fun <T> updateItem(
        cell: Cell<T>,
        converter: StringConverter<T>?,
        choiceBox: ChoiceBox<T>?
    ) {
        updateItem(cell, converter, null, null, choiceBox)
    }

    fun <T> updateItem(
        cell: Cell<T>,
        converter: StringConverter<T>?,
        hbox: HBox?,
        graphic: Node?,
        choiceBox: ChoiceBox<T>?
    ) {
        if (cell.isEmpty) {
            cell.text = null
            cell.graphic = null
        } else {
            if (cell.isEditing) {
                choiceBox?.selectionModel?.select(cell.item)
                cell.text = null

                if (graphic != null) {
                    hbox!!.children.setAll(graphic, choiceBox)
                    cell.graphic = hbox
                } else {
                    cell.graphic = choiceBox
                }
            } else {
                cell.text = getItemText(cell, converter)
                cell.graphic = graphic
            }
        }
    }

    fun <T> createChoiceBox(
        cell: Cell<T>,
        items: ObservableList<T>?,
        converter: ObjectProperty<StringConverter<T>?>?
    ): ChoiceBox<T> {
        val choiceBox = ChoiceBox(items)
        choiceBox.maxWidth = Double.MAX_VALUE
        choiceBox.converterProperty().bind(converter)
        choiceBox.selectionModel.selectedItemProperty()
            .addListener { ov: ObservableValue<out T>?, oldValue: T, newValue: T ->
                if (cell.isEditing) {
                    cell.commitEdit(newValue)
                }
            }
        return choiceBox
    }


    /***************************************************************************
     * *
     * TextField convenience                                                   *
     * *
     */
    fun <T> updateItem(
        cell: Cell<T>,
        converter: StringConverter<T>?,
        textField: TextField?
    ) {
        updateItem(cell, converter, null, null, textField)
    }

    fun <T> updateItem(
        cell: Cell<T>,
        converter: StringConverter<T>?,
        hbox: HBox?,
        graphic: Node?,
        textField: TextField?
    ) {
        if (cell.isEmpty) {
            cell.text = null
            cell.graphic = null
        } else {
            if (cell.isEditing) {
                if (textField != null) {
                    textField.text = getItemText<T>(cell, converter)
                }
                cell.text = null

                if (graphic != null) {
                    hbox!!.children.setAll(graphic, textField)
                    cell.graphic = hbox
                } else {
                    cell.graphic = textField
                }
            } else {
                cell.text = getItemText<T>(cell, converter)
                cell.graphic = graphic
            }
        }
    }

    fun <T> startEdit(
        cell: Cell<T>,
        converter: StringConverter<T>?,
        hbox: HBox?,
        graphic: Node?,
        textField: TextField?
    ) {
        if (textField != null) {
            textField.text = getItemText<T>(cell, converter)
        }
        cell.text = null

        if (graphic != null) {
            hbox!!.children.setAll(graphic, textField)
            cell.graphic = hbox
        } else {
            cell.graphic = textField
        }

        textField!!.selectAll()

        // requesting focus so that key input can immediately go into the
        // TextField (see RT-28132)
        textField.requestFocus()
    }

    fun <T> cancelEdit(cell: Cell<T>, converter: StringConverter<T>?, graphic: Node?) {
        cell.text = getItemText<T>(cell, converter)
        cell.graphic = graphic
    }

    fun <T> createTextField(cell: Cell<T>, converter: StringConverter<T>?): TextField {
        val textField = TextField(getItemText<T>(cell, converter))

        // Use onAction here rather than onKeyReleased (with check for Enter),
        // as otherwise we encounter RT-34685
        textField.onAction = EventHandler { event: ActionEvent ->
            checkNotNull(converter) {
                ("Attempting to convert text input into Object, but provided "
                        + "StringConverter is null. Be sure to set a StringConverter "
                        + "in your cell factory.")
            }
            cell.commitEdit(converter.fromString(textField.text))
            event.consume()
        }
        textField.onKeyReleased = EventHandler { t: KeyEvent ->
            if (t.code == KeyCode.ESCAPE) {
                cell.cancelEdit()
                t.consume()
            }
        }
        return textField
    }


    /***************************************************************************
     * *
     * ComboBox convenience                                                   *
     * *
     */
    fun <T> updateItem(cell: Cell<T>, converter: StringConverter<T>?, comboBox: ComboBox<T>?) {
        updateItem(cell, converter, null, null, comboBox)
    }

    fun <T> updateItem(
        cell: Cell<T>,
        converter: StringConverter<T>?,
        hbox: HBox?,
        graphic: Node?,
        comboBox: ComboBox<T>?
    ) {
        if (cell.isEmpty) {
            cell.text = null
            cell.graphic = null
        } else {
            if (cell.isEditing) {
                comboBox?.selectionModel?.select(cell.item)
                cell.text = null

                if (graphic != null) {
                    hbox!!.children.setAll(graphic, comboBox)
                    cell.graphic = hbox
                } else {
                    cell.graphic = comboBox
                }
            } else {
                cell.text = getItemText<T>(cell, converter)
                cell.graphic = graphic
            }
        }
    }

    fun <T> createComboBox(
        cell: Cell<T>,
        items: ObservableList<T>?,
        converter: ObjectProperty<StringConverter<T>?>?
    ): ComboBox<T> {
        val comboBox = ComboBox(items)
        comboBox.converterProperty().bind(converter)
        comboBox.maxWidth = Double.MAX_VALUE
        comboBox.selectionModel.selectedItemProperty()
            .addListener { ov: ObservableValue<out T>?, oldValue: T, newValue: T ->
                if (cell.isEditing) {
                    cell.commitEdit(newValue)
                }
            }
        return comboBox
    }
}
