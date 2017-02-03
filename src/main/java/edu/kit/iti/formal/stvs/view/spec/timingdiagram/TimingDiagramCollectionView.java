package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramView;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.geometry.Bounds;
import javafx.geometry.Insets;
import javafx.scene.chart.NumberAxis;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 09.01.17.
 */
public class TimingDiagramCollectionView extends VBox {
  private ScrollPane scrollPane = new ScrollPane();
  private VBox diagramContainer = new VBox();
  private HBox globalAxisContainer = new HBox();
  private NumberAxis numberAxis = new NumberAxis(0, 10, 1);
  public TimingDiagramCollectionView(){
    super();
    getChildren().addAll(scrollPane, globalAxisContainer);
    globalAxisContainer.getChildren().add(numberAxis);
    globalAxisContainer.setPadding(new Insets(0,0,0,40));
    setPadding(new Insets(0,10,0,10));
    scrollPane.setContent(diagramContainer);
    scrollPane.setFitToWidth(true);
    diagramContainer.widthProperty().addListener(change -> {
      Bounds viewportBounds = scrollPane.getViewportBounds();
      numberAxis.setPrefWidth(viewportBounds.getWidth()-40);
    });
    numberAxis.setMinHeight(30);
    scrollPane.getStyleClass().add("noborder-scroll-pane");
    this.getStylesheets().add(
        TimingDiagramCollectionView.class.getResource("style.css").toExternalForm()
    );
  }
  public VBox getDiagramContainer(){
    return diagramContainer;
  }

  public NumberAxis getNumberAxis() {
    return numberAxis;
  }
}
