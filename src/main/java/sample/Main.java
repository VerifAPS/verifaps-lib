package sample;

import javafx.application.Application;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.chart.NumberAxis;
import javafx.scene.chart.XYChart;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;
import org.fxmisc.richtext.InlineStyleTextArea;
import org.fxmisc.richtext.LineNumberFactory;

import java.util.ArrayList;

public class Main extends Application {

    private InlineStyleTextArea<EditorTextStyle> textArea;

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


        textArea = new InlineStyleTextArea<>(new EditorTextStyle(), EditorTextStyle::toCss);
        textArea.setId("textArea");
        AnchorPane anchorPaneLeft = (AnchorPane) scene.lookup("#anchorpane_left");
        anchorPaneLeft.getChildren().add(textArea);
        AnchorPane.setBottomAnchor(textArea, 0.0);
        AnchorPane.setTopAnchor(textArea, 0.0);
        AnchorPane.setLeftAnchor(textArea, 0.0);
        AnchorPane.setRightAnchor(textArea, 0.0);
        textArea.setParagraphGraphicFactory(LineNumberFactory.get(textArea));

        textArea.setOnMouseClicked(event -> {
            EditorTextStyle css = EditorTextStyle.random();
            System.out.println(css);
            textArea.setStyle(0, textArea.getText().length(), css);
        });
    }

    public InlineStyleTextArea<EditorTextStyle> getTextArea() {
        return textArea;
    }


    public static void main(String[] args) {
        launch(args);
    }
}
