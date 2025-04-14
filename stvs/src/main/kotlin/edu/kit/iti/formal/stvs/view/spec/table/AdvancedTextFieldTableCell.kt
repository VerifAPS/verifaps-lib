package edu.kit.iti.formal.stvs.view.spec.table

import javafx.application.Platform
import javafx.beans.property.ObjectProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.beans.value.ObservableValue
import javafx.event.EventHandler
import javafx.scene.control.TableCell
import javafx.scene.control.TableColumn
import javafx.scene.control.TableView
import javafx.scene.control.TextField
import javafx.scene.control.cell.TextFieldTableCell
import javafx.scene.input.KeyCode
import javafx.scene.input.KeyEvent
import javafx.util.Callback
import javafx.util.StringConverter

/**
 * Created by Lukas on 13.07.2017.
 */
open class AdvancedTextFieldTableCell<S, T> @JvmOverloads constructor(converter: StringConverter<T>? = null) :
    TableCell<S, T>() {

    var textField: TextField? = null

    fun setUp() {
        textField?.onKeyPressed = EventHandler { t: KeyEvent ->
            when (t.code) {
                KeyCode.ENTER ->
                    commitEdit(converter.get()!!.fromString(textField?.text))

                KeyCode.ESCAPE ->
                    cancelEdit()

                KeyCode.TAB -> {
                    commitEdit(converter.get()!!.fromString(textField?.text))
                    selectNextTableCell(!t.isShiftDown)
                }

                else -> {}
            }
        }
    }

    private fun selectNextTableCell(forward: Boolean) {
        var nextColumn = getNextColumn(forward)
        var nextRowIndex = tableRow.index
        //current column is at the end / start of the table
        if (nextColumn == null) {
            // move to the next row, when direction is forward; backward if direction is backward
            nextRowIndex += (if (forward) 1 else -1)
            //if forward? -> use 1 as next Column (since the 0th Column is assumed to not be editable
            //if !forward? -> use last column in table
            nextColumn = tableView.columns[if (forward) 1 else tableView.columns.size - 1]
        }
        tableView.edit(nextRowIndex, nextColumn)
    }

    /**
     * getNextColumn: get the next (previous) Column relative to this TableCell.
     *
     * @param forward should it return the next or previous Column?
     * @return next (previous) TableColumn or null if none exists in this row
     */
    private fun getNextColumn(forward: Boolean): TableColumn<S?, *>? {
        val columns: MutableList<TableColumn<S?, *>> = ArrayList()
        columns.addAll(tableView.columns)

        // There is no other column that supports editing.
        if (columns.size < 2) {
            return null
        }
        val currentIndex = columns.indexOf(tableColumn)
        var nextIndex = currentIndex
        if (forward) {
            nextIndex++
            if (nextIndex > columns.size - 1) {
                return null
            }
        } else {
            nextIndex--
            //assumes, that the first column is not editable
            if (nextIndex < 1) {
                return null
            }
        }
        return columns[nextIndex]
    }


    /***************************************************************************
     * *
     * Properties                                                              *
     * *
     */
    // --- converter
    private val converter: ObjectProperty<StringConverter<T>?> = SimpleObjectProperty(
        this, "converter"
    )

    /**
     * Creates a TextFieldTableCell that provides a [TextField] when put
     * into editing mode that allows editing of the cell content. This method
     * will work on any TableColumn instance, regardless of its generic type.
     * However, to enable this, a [StringConverter] must be provided that
     * will convert the given String (from what the user typed in) into an
     * instance of type T. This item will then be passed along to the
     * [TableColumn.onEditCommitProperty] callback.
     *
     * @param converter A [converter][StringConverter] that can convert
     * the given String (from what the user typed in) into an instance of
     * type T.
     */
    /***************************************************************************
     * *
     * Constructors                                                            *
     * *
     */
    /**
     * Creates a default TextFieldTableCell with a null converter. Without a
     * [StringConverter] specified, this cell will not be able to accept
     * input from the TextField (as it will not know how to convert this back
     * to the domain object). It is therefore strongly encouraged to not use
     * this constructor unless you intend to set the converter separately.
     */
    init {
        styleClass.add("text-field-table-cell")
        Platform.runLater {}

        setConverter(converter)
    }

    /**
     * The [StringConverter] property.
     */
    fun converterProperty(): ObjectProperty<StringConverter<T>?> {
        return converter
    }

    /**
     * Sets the [StringConverter] to be used in this cell.
     */
    fun setConverter(value: StringConverter<T>?) {
        converterProperty().set(value)
    }

    /**
     * Returns the [StringConverter] used in this cell.
     */
    fun getConverter(): StringConverter<T>? {
        return converterProperty().get()
    }


    /***************************************************************************
     * *
     * Public API                                                              *
     * *
     */
    /**
     * {@inheritDoc}
     */
    override fun startEdit() {
        if (!isEditable
            || !tableView.isEditable
            || !tableColumn.isEditable
        ) {
            return
        }
        super.startEdit()


        if (isEditing) {
            if (textField == null) {
                textField = AdvancedCellUtils.createTextField(this, getConverter())
                textField?.focusedProperty()
                    ?.addListener { observable: ObservableValue<out Boolean?>?, oldValue: Boolean?, newValue: Boolean? ->
                        if (!newValue!!) {
                            commitEdit(converter.get()!!.fromString(textField?.text))
                        }
                    }
                setUp()
            }

            AdvancedCellUtils.startEdit(this, getConverter(), null, null, textField)
        }
    }

    /**
     * {@inheritDoc}
     */
    override fun cancelEdit() {
        super.cancelEdit()
        AdvancedCellUtils.cancelEdit(this, getConverter(), null)
    }

    /**
     * {@inheritDoc}
     */
    public override fun updateItem(item: T, empty: Boolean) {
        super.updateItem(item, empty)
        AdvancedCellUtils.updateItem(this, getConverter(), null, null, textField)
    }

    companion object {
        /***************************************************************************
         * *
         * Static cell factories                                                   *
         * *
         */
        /**
         * Provides a [TextField] that allows editing of the cell content when
         * the cell is double-clicked, or when
         * [TableView.edit] is called.
         * This method will only  work on [TableColumn] instances which are of
         * type String.
         *
         * @return A [Callback] that can be inserted into the
         * [cell factory property][TableColumn.cellFactoryProperty] of a
         * TableColumn, that enables textual editing of the content.
         */
        /*fun <S> forTableColumn(): Callback<TableColumn<S, String>, TableCell<S, String>> {
            return forTableColumn(DefaultStringConverter())
        }*/

        /**
         * Provides a [TextField] that allows editing of the cell content when
         * the cell is double-clicked, or when
         * [TableView.edit] is called.
         * This method will work  on any [TableColumn] instance, regardless of
         * its generic type. However, to enable this, a [StringConverter] must
         * be provided that will convert the given String (from what the user typed
         * in) into an instance of type T. This item will then be passed along to the
         * [TableColumn.onEditCommitProperty] callback.
         *
         * @param converter A [StringConverter] that can convert the given String
         * (from what the user typed in) into an instance of type T.
         * @return A [Callback] that can be inserted into the
         * [cell factory property][TableColumn.cellFactoryProperty] of a
         * TableColumn, that enables textual editing of the content.
         */
        fun <S, T> forTableColumn(
            converter: StringConverter<T>?
        ): Callback<TableColumn<S, T>, TableCell<S?, T>> {
            return Callback { list: TableColumn<S, T>? -> TextFieldTableCell(converter) }
        }
    }
}
