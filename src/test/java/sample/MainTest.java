package sample;

import javafx.stage.Stage;
import org.junit.Test;
import org.testfx.framework.junit.ApplicationTest;

import static javafx.scene.input.KeyCode.ENTER;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.testfx.api.FxAssert.verifyThat;

/**
 * Created by Philipp on 08.11.2016.
 */
public class MainTest extends ApplicationTest {

    private Main mainScene;

    @Override
    public void start(Stage stage) throws Exception {
        stage.setAlwaysOnTop(true);
        mainScene = new Main();
        mainScene.start(stage);
    }

    @Test
    public void testTextArea() {
        String testString0 = "This is a test";
        String testString1 = "for the javafx test framework";

        clickOn("#textArea");
        write(testString0);
        push(ENTER);
        write(testString1);

        assertEquals(
                "The Strings were written to the textArea",
                mainScene.getTextArea().getDocument().getText(),
                testString0 + "\n" + testString1);
    }
}
