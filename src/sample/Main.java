package sample;

import javafx.application.Application;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.embed.swing.SwingNode;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SyntaxConstants;
import org.fife.ui.rtextarea.RTextScrollPane;

import java.util.ArrayList;

public class Main extends Application {

    @Override
    public void start(Stage primaryStage) throws Exception{
        Parent root = FXMLLoader.load(getClass().getResource("sample.fxml"));
        primaryStage.setTitle("Hello World");
        Scene scene = new Scene(root, 800, 600);
        primaryStage.setScene(scene);
        primaryStage.show();

        Pane pane = (Pane) scene.lookup("#timingdiagram");
        TimingChart tc = new TimingChart(new NumberAxis(), new NumberAxis());
        XYChart.Series<Integer, Integer> series = new XYChart.Series<Integer, Integer>(FXCollections.observableList(new ArrayList<>()));
        ObservableList<XYChart.Series<Integer, Integer>> seriesCollection = FXCollections.observableList(new ArrayList<>());
        seriesCollection.add(series);
        tc.setData(seriesCollection);
        series.getData().add(new XYChart.Data<>(10,10));
        series.getData().add(new XYChart.Data<>(20,10));
        series.getData().add(new XYChart.Data<>(40,30));
        tc.prefWidthProperty().bind(pane.widthProperty());
        tc.prefHeightProperty().bind(pane.heightProperty());
        pane.getChildren().add(tc);

        SwingNode swingNode = (SwingNode) scene.lookup("#swingnode");

        RSyntaxTextArea textArea = new RSyntaxTextArea(20, 60);
        textArea.setSyntaxEditingStyle(SyntaxConstants.SYNTAX_STYLE_JAVA);
        textArea.setCodeFoldingEnabled(true);
        RTextScrollPane sp = new RTextScrollPane(textArea);

        swingNode.setContent(sp);

        AnchorPane anchorPane = (AnchorPane) scene.lookup("#anchorpane_left");
        ChangeListener<Number> repaintOnChangeSizeListener = new ChangeListener<Number>() {
            @Override
            public void changed(ObservableValue<? extends Number> observable, Number oldValue, Number newValue) {
                swingNode.getContent().repaint();
            }
        };
        anchorPane.widthProperty().addListener(repaintOnChangeSizeListener);
        anchorPane.heightProperty().addListener(repaintOnChangeSizeListener);
    }


    public static void main(String[] args) {
        launch(args);
    }
}
