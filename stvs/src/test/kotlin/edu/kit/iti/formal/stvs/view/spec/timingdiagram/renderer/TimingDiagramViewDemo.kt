package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.scene.Scene
import org.junit.Ignore
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import java.util.function.Supplier

/**
 * Created by leonk on 02.02.2017.
 */
@Tag("demo")
class TimingDiagramViewDemo {
    @Ignore
    @Test
    fun javaFxTest() {
        JavaFxTest.Companion.runView(Supplier<Scene?> { this.simpleScene() })
    }

    private fun simpleScene(): Scene? {
        /*TimingDiagramController controller = new TimingDiagramController(new NumberAxis(),new NumberAxis());
    Pane pane = new Pane();
    pane.getChildren().add(controller.getView());
    Scene scene = new Scene(pane, 800, 600);
    //scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
    return scene;*/
        return null
    }
}