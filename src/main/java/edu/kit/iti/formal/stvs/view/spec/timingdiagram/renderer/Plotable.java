package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import javafx.scene.chart.XYChart;

import java.util.List;

/**
 * Created by leonk on 05.02.2017.
 */
public class Plotable {
  public static XYChart.Series<Number, String> toStringSeries(List<ConcreteCell> concreteCells){
    XYChart.Series<Number, String> dataSeries = new XYChart.Series<>();
    for(int i = 0; i<concreteCells.size(); i++){
      String cellAsString = concreteCells.get(i).getValue().getValueString();
      dataSeries.getData().add(new XYChart.Data<>(i, cellAsString));
    }
    return dataSeries;
  }

  public static XYChart.Series<Number, Number> toNumberSeries(List<ConcreteCell> concreteCells){
    XYChart.Series<Number, Number> dataSeries = new XYChart.Series<>();
    for(int i = 0; i<concreteCells.size(); i++){
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