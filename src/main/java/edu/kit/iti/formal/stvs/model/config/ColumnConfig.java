package edu.kit.iti.formal.stvs.model.config;

import javafx.beans.property.DoubleProperty;
import javafx.beans.property.SimpleDoubleProperty;

/**
 * Configuration for table column. Contains GUI-related information about a column.
 *
 * @author Philipp
 */
public class ColumnConfig {
  private DoubleProperty width;

  /**
   * Default ColumnConfig.
   */
  public ColumnConfig() {
    width = new SimpleDoubleProperty(100);
  }

  /**
   * Create a new ColumnConfig.
   *
   * @param colwidth The initial column width
   */
  public ColumnConfig(double colwidth) {
    if (colwidth <= 0) {
      throw new IllegalArgumentException("Column width must be positive");
    }
    width = new SimpleDoubleProperty(colwidth);
  }

  /**
   * Get the current column width.
   *
   * @return The current column width
   */
  public double getWidth() {
    return width.get();
  }

  /**
   * Set the current column width.
   *
   * @param width The current column width
   */
  public void setWidth(double width) {
    if (width <= 0) {
      throw new IllegalArgumentException("Column width must be positive");
    }
    this.width.set(width);
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (!(obj instanceof ColumnConfig)) {
      return false;
    }

    ColumnConfig that = (ColumnConfig) obj;

    return width.get() == that.width.get();
  }

  @Override
  public int hashCode() {
    long bits = Double.doubleToRawLongBits(width.get());
    return (int) (bits ^ (bits >> 32));
  }

  public DoubleProperty widthProperty() {
    return width;
  }
}
