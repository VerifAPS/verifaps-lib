package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.application.Platform;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.control.TableCell;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.TextField;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.KeyCode;
import javafx.util.Callback;
import javafx.util.StringConverter;
import javafx.util.converter.DefaultStringConverter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Created by Lukas on 13.07.2017.
 */
public class AdvancedTextFieldTableCell<S, T> extends TableCell<S, T> {
  /***************************************************************************
   *                                                                         *
   * Static cell factories                                                   *
   *                                                                         *
   **************************************************************************/

  /**
   * Provides a {@link TextField} that allows editing of the cell content when
   * the cell is double-clicked, or when
   * {@link TableView#edit(int, javafx.scene.control.TableColumn)} is called.
   * This method will only  work on {@link TableColumn} instances which are of
   * type String.
   *
   * @return A {@link Callback} that can be inserted into the
   * {@link TableColumn#cellFactoryProperty() cell factory property} of a
   * TableColumn, that enables textual editing of the content.
   */
  public static <S> Callback<TableColumn<S, String>, TableCell<S, String>> forTableColumn() {
    return forTableColumn(new DefaultStringConverter());
  }

  /**
   * Provides a {@link TextField} that allows editing of the cell content when
   * the cell is double-clicked, or when
   * {@link TableView#edit(int, javafx.scene.control.TableColumn) } is called.
   * This method will work  on any {@link TableColumn} instance, regardless of
   * its generic type. However, to enable this, a {@link StringConverter} must
   * be provided that will convert the given String (from what the user typed
   * in) into an instance of type T. This item will then be passed along to the
   * {@link TableColumn#onEditCommitProperty()} callback.
   *
   * @param converter A {@link StringConverter} that can convert the given String
   *                  (from what the user typed in) into an instance of type T.
   * @return A {@link Callback} that can be inserted into the
   * {@link TableColumn#cellFactoryProperty() cell factory property} of a
   * TableColumn, that enables textual editing of the content.
   */
  public static <S, T> Callback<TableColumn<S, T>, TableCell<S, T>> forTableColumn(
      final StringConverter<T> converter) {
    return list -> new TextFieldTableCell<S, T>(converter);
  }


  /***************************************************************************
   *                                                                         *
   * Fields                                                                  *
   *                                                                         *
   **************************************************************************/

  public TextField textField;

  public void setUp() {
    textField.setOnKeyPressed(t -> {
      if (t.getCode() == KeyCode.ENTER) {
        commitEdit(converter.get().fromString(textField.getText()));
      } else if (t.getCode() == KeyCode.ESCAPE) {
        cancelEdit();
      } else if (t.getCode() == KeyCode.TAB) {
        commitEdit(converter.get().fromString(textField.getText()));

        selectNextTableCell(!t.isShiftDown());
      }
    });
  }

  private void selectNextTableCell(boolean forward) {
    TableColumn<S, ?> nextColumn = getNextColumn(forward);
    int nextRowIndex = getTableRow().getIndex();
    //current column is at the end / start of the table
    if (nextColumn == null) {
      // move to the next row, when direction is forward; backward if direction is backward
      nextRowIndex += (forward ? 1 : -1);
      //if forward? -> use 1 as next Column (since the 0th Column is assumed to not be editable
      //if !forward? -> use last column in table
      nextColumn = getTableView().getColumns().get(forward ? 1 : getTableView().getColumns().size() - 1);
    }
    getTableView().edit(nextRowIndex, nextColumn);
  }

  /**
   * getNextColumn: get the next (previous) Column relative to this TableCell.
   *
   * @param forward should it return the next or previous Column?
   * @return next (previous) TableColumn or null if none exists in this row
   */
  private TableColumn<S, ?> getNextColumn(boolean forward) {
    List<TableColumn<S, ?>> columns = new ArrayList<>();
    columns.addAll(getTableView().getColumns());

    // There is no other column that supports editing.
    if (columns.size() < 2) {
      return null;
    }
    int currentIndex = columns.indexOf(getTableColumn());
    int nextIndex = currentIndex;
    if (forward) {
      nextIndex++;
      if (nextIndex > columns.size() - 1) {
        return null;
      }
    } else {
      nextIndex--;
      //assumes, that the first column is not editable
      if (nextIndex < 1) {
        return null;
      }
    }
    return columns.get(nextIndex);
  }


  /***************************************************************************
   *                                                                         *
   * Constructors                                                            *
   *                                                                         *
   **************************************************************************/

  /**
   * Creates a default TextFieldTableCell with a null converter. Without a
   * {@link StringConverter} specified, this cell will not be able to accept
   * input from the TextField (as it will not know how to convert this back
   * to the domain object). It is therefore strongly encouraged to not use
   * this constructor unless you intend to set the converter separately.
   */
  public AdvancedTextFieldTableCell() {
    this(null);
  }

  /**
   * Creates a TextFieldTableCell that provides a {@link TextField} when put
   * into editing mode that allows editing of the cell content. This method
   * will work on any TableColumn instance, regardless of its generic type.
   * However, to enable this, a {@link StringConverter} must be provided that
   * will convert the given String (from what the user typed in) into an
   * instance of type T. This item will then be passed along to the
   * {@link TableColumn#onEditCommitProperty()} callback.
   *
   * @param converter A {@link StringConverter converter} that can convert
   *                  the given String (from what the user typed in) into an instance of
   *                  type T.
   */
  public AdvancedTextFieldTableCell(StringConverter<T> converter) {
    this.getStyleClass().add("text-field-table-cell");
    Platform.runLater(() -> {
        }

    );

    setConverter(converter);
  }


  /***************************************************************************
   *                                                                         *
   * Properties                                                              *
   *                                                                         *
   **************************************************************************/

  // --- converter
  private ObjectProperty<StringConverter<T>> converter =
      new SimpleObjectProperty<StringConverter<T>>(this, "converter");

  /**
   * The {@link StringConverter} property.
   */
  public final ObjectProperty<StringConverter<T>> converterProperty() {
    return converter;
  }

  /**
   * Sets the {@link StringConverter} to be used in this cell.
   */
  public final void setConverter(StringConverter<T> value) {
    converterProperty().set(value);
  }

  /**
   * Returns the {@link StringConverter} used in this cell.
   */
  public final StringConverter<T> getConverter() {
    return converterProperty().get();
  }


  /***************************************************************************
   *                                                                         *
   * Public API                                                              *
   *                                                                         *
   **************************************************************************/

  /**
   * {@inheritDoc}
   */
  @Override
  public void startEdit() {
    if (!isEditable()
        || !getTableView().isEditable()
        || !getTableColumn().isEditable()) {
      return;
    }
    super.startEdit();


    if (isEditing()) {
      if (textField == null) {
        textField = AdvancedCellUtils.createTextField(this, getConverter());
        this.textField.focusedProperty().addListener((observable, oldValue, newValue) -> {
              if (!newValue) {
                commitEdit(converter.get().fromString(textField.getText()));
              }
            }
        );
        setUp();
      }

      AdvancedCellUtils.startEdit(this, getConverter(), null, null, textField);
    }
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public void cancelEdit() {
    super.cancelEdit();
    AdvancedCellUtils.cancelEdit(this, getConverter(), null);
  }

  /**
   * {@inheritDoc}
   */
  @Override
  public void updateItem(T item, boolean empty) {
    super.updateItem(item, empty);
    AdvancedCellUtils.updateItem(this, getConverter(), null, null, textField);
  }
}
