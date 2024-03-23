package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.table.ConcreteCell;

import java.util.List;

import javafx.scene.chart.XYChart;

/**
 * Converts lists of {@link ConcreteCell ConcreteCells} to {@link javafx.scene.chart.XYChart.Series}
 *
 * @author Leon Kaucher
 */
public class Plotable {
  /**
   * Converts a list of concrete cells to a string series.
   * This method is used to generate category chart series.
   * It simply converts every data point into its string representation.
   *
   * @param concreteCells cells to convert
   * @return converted series
   */
  public static XYChart.Series<Number, String> toStringSeries(List<ConcreteCell> concreteCells) {
    XYChart.Series<Number, String> dataSeries = new XYChart.Series<>();
    for (int i = 0; i < concreteCells.size(); i++) {
      String cellAsString = concreteCells.get(i).getValue().getValueString();
      dataSeries.getData().add(new XYChart.Data<>(i, cellAsString));
    }
    return dataSeries;
  }

  /**
   * Converts a list of concrete cells to a number series.
   * This method is used to generate number chart series.
   * It converts the cells to numbers depending on their type.
   * @param concreteCells cells to convert
   * @return converted series
   */
  public static XYChart.Series<Number, Number> toNumberSeries(List<ConcreteCell> concreteCells) {
    XYChart.Series<Number, Number> dataSeries = new XYChart.Series<>();
    for (int i = 0; i < concreteCells.size(); i++) {
      Number cellAsNumber = concreteCells.get(i).getValue().match(
          integer -> integer,
          bool -> bool ? 1 : 0,
          valueEnum -> valueEnum.getType().getValues().indexOf(valueEnum)
      );
      dataSeries.getData().add(new XYChart.Data<>(i, cellAsNumber));
    }
    return dataSeries;
  }
}
