package edu.kit.iti.formal.stvs;

import com.sun.javafx.application.LauncherImpl;
import edu.kit.iti.formal.stvs.view.StvsMainScene;
import edu.kit.iti.formal.stvs.view.StvsPreloader;
import edu.kit.iti.formal.stvs.view.common.HostServiceSingleton;
import edu.kit.iti.formal.stvs.view.menu.WelcomeWizard;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.TitledPane;
import javafx.scene.image.Image;
import javafx.scene.input.MouseEvent;
import javafx.stage.Stage;
import org.fxmisc.cssfx.CSSFX;

import java.util.Locale;

/**
 * The entry point to ST Verification Studio.
 *
 * @author Leon Kaucher
 */
public class StvsApplication extends Application {

    private StvsMainScene mainScene = new StvsMainScene();
    private Stage primaryStage;

    /**
     * Launch the application.
     *
     * @param args The command-line arguments passed to the application
     */
    public static void main(String[] args) {
        Locale.setDefault(Locale.ENGLISH);
        LauncherImpl.launchApplication(StvsApplication.class, StvsPreloader.class, args);
    }

    @Override
    public void start(Stage primaryStage) {
        HostServiceSingleton.setInstance(getHostServices()); //weigl: ???
        this.mainScene = new StvsMainScene();
        this.primaryStage = new Stage();
        Platform.setImplicitExit(true);
        primaryStage.setTitle(StvsVersion.getWindowTitle());
        primaryStage.setScene(mainScene.getScene());
        primaryStage.setMaximized(mainScene.shouldBeMaximizedProperty().get());
        primaryStage.getIcons().addAll(
                new Image(StvsApplication.class.getResourceAsStream("logo_large.png")),
                new Image(StvsApplication.class.getResourceAsStream("logo.png")));
        mainScene.shouldBeMaximizedProperty().bind(primaryStage.maximizedProperty());

        mainScene.getScene().getStylesheets().add(
                StvsApplication.class.getResource("normal.css").toExternalForm()
        );

        CSSFX.start(mainScene.getScene());

        //Debugger snippet for finding the styleclasses for the node under cursor.
        mainScene.getScene().addEventFilter(MouseEvent.MOUSE_MOVED, mouseEvent -> {
            if (mouseEvent.isAltDown() && mouseEvent.isControlDown()) {
                try {
                    Node node = (Node) mouseEvent.getTarget();
                    ObservableList<String> classes = node.getStyleClass();
                    System.out.println("Classes of " + node.getClass().getSimpleName() + " are " + classes);
                    System.out.println("Style of " + node.getClass().getSimpleName() + ": " + node.getStyle());

                    System.out.println(((TitledPane) node).getAlignment());
                    System.out.println(((TitledPane) node).getTextAlignment());

                } catch (ClassCastException e) {

                }
            }
        });


        if (System.getProperty("presentation-mode", "false").equals("true")) {
            mainScene.getScene().getStylesheets().add(
                    StvsApplication.class.getResource("presentation.css").toExternalForm()
            );
        }

        if (mainScene.getRootController().getRootModel().isFirstStart()) {
            new WelcomeWizard(mainScene.getRootController().getRootModel().getGlobalConfig())
                    .showAndWait();
        }

        primaryStage.show();
    }

    @Override
    public void stop() {
        mainScene.onClose();
        this.primaryStage.hide();
        System.exit(0);
    }
}
