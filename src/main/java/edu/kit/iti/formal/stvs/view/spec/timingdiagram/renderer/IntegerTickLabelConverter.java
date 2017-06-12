package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.ValueAxis;
import javafx.util.StringConverter;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Created by csicar on 12.06.17.
 * Converts between Numbers and Strings
 * This class is used for the TickLabels on a NumberAxis, that should display only Integers.
 *
 */
/*
  based on: based on: https://stackoverflow.com/questions/23841268/how-to-make-javafx-chart-numberaxis-only-show-integer-value-not-double
  this approach was taken instead of extending the ValueAxis, because the required functionality
  that has to be implemented for implementing ValueAxis is quite involved (deciding how many
  tick-marks should be displayed, given a certain height of the widget, etc.)
 */
public class IntegerTickLabelConverter extends StringConverter<Number> {

  @Override
  public String toString(Number number) {
    if (number.intValue() == number.doubleValue()) {
      return ""+number;
    }
    return "";
  }

  @Override
  public Number fromString(String s) {
    Number value = Double.parseDouble(s);
    return value;
  }
}
