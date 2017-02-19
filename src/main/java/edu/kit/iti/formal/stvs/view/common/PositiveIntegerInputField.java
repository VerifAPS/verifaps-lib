package edu.kit.iti.formal.stvs.view.common;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ObservableValue;
import javafx.geometry.Pos;
import javafx.scene.control.TextField;

import java.util.Optional;

/**
 * Created by csicar on 15.02.17.
 * @author Carsten Csiky
 */
public class PositiveIntegerInputField extends TextField {
  private BooleanProperty valid;

  public PositiveIntegerInputField() {
    this.textProperty().addListener(this::onInputChange);
    valid = new SimpleBooleanProperty();
    valid.addListener(this::onValidStateChange);
    this.alignmentProperty().setValue(Pos.CENTER_RIGHT);
  }

  private void onValidStateChange(ObservableValue<?> observableValue, Boolean old, Boolean
      value) {
    if (value) {
      this.getStyleClass().add("valid");
    } else {
      this.getStyleClass().remove("valid");
    }
  }

  private void onInputChange(ObservableValue<?> observableValue, String old, String newValue) {
    valid.set(getText().trim().matches("(?!0)[0-9]+"));
  }

  /**
   * get inputfield value as an integer
   * if no integer representation is available Optional.empty() will be returned
   * @return value as an integer
   */
  public Optional<Integer> getInteger() {
    if (valid.get()) {
      return Optional.of(Integer.valueOf(this.getText().trim()));
    } else {
      return Optional.empty();
    }
  }

  public boolean isValid() {
    return valid.get();
  }

  public BooleanProperty validProperty() {
    return valid;
  }
}
