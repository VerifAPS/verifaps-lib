package sample;

import javafx.application.Application;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;

import java.util.ArrayList;

public class Main extends Application {

    @Override
    public void start(Stage primaryStage) throws Exception{
        Parent root = FXMLLoader.load(getClass().getResource("sample.fxml"));
        primaryStage.setTitle("Hello World");
        Scene scene = new Scene(root, 300, 275);
        primaryStage.setScene(scene);
        primaryStage.show();

        Pane pane = (Pane) scene.lookup("#timingdiagram");
        TimingChart tc = new TimingChart(new NumberAxis(), new NumberAxis());
        XYChart.Data<Integer, Integer> data = new XYChart.Data<>(1,1);
        XYChart.Series<Integer, Integer> series = new XYChart.Series<Integer, Integer>(FXCollections.observableList(new ArrayList<>()));
        series.getData().add(data);
        ObservableList<XYChart.Series<Integer, Integer>> seriesCollection = FXCollections.observableList(new ArrayList<>());
        seriesCollection.add(series);
        tc.setData(seriesCollection);
        tc.prefWidthProperty().bind(pane.widthProperty());
        tc.prefHeightProperty().bind(pane.heightProperty());
        pane.getChildren().add(tc);
    }


    public static void main(String[] args) {
        launch(args);
    }
}
