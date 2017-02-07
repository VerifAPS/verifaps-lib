package edu.kit.iti.formal.stvs.model.config;

/**
 * Configuration for table column. Contains GUI-related information about a column
 */
public class ColumnConfig {
  private int width;

  /**
   * Default ColumnConfig
   */
  public ColumnConfig() {
    width = 20;
  }

  /**
   * Create a new ColumnConfig
   *
   * @param colwidth The initial column width
   */
  public ColumnConfig(int colwidth) {
    width = colwidth;
  }

  /**
   * Get the current column width
   *
   * @return The current column width
   */
  public int getWidth() {
    return width;
  }

  /**
   * Set the current column width
   *
   * @param width The current column width
   */
  public void setWidth(int width) {
    this.width = width;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof ColumnConfig)) return false;

    ColumnConfig that = (ColumnConfig) o;

    return width == that.width;
  }

  @Override
  public int hashCode() {
    return width;
  }
}