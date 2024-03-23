package edu.kit.iti.formal.stvs.view;

import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.TableView;
import javafx.scene.transform.Affine;
import javafx.scene.transform.Transform;
import javafx.scene.web.WebView;
import javafx.stage.Stage;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * Provides static methods for view operations.
 *
 * @author Benjamin Alt
 */
public class ViewUtils {
    public static final Logger LOGGER = LoggerFactory.getLogger(ViewUtils.class);

    //hack for getting the auto resizing
    //see https://stackoverflow.com/questions/23284437/javafx-tablecolumn-resize-to-fit-cell-content
    private static Method columnToFitMethod;

    static {
        //TODO
        //columnToFitMethod = TableViewSkin.class.getDeclaredMethod("resizeColumnToFitContent", TableColumn.class, int.class);
        //columnToFitMethod.setAccessible(true);
    }

    /**
     * Calculates the {@link Transform Transformation} from children node coordinates to
     * parent node coordinates.
     * <p>
     * {@code child} must be a direct or indirect child of {@code rootOfCalculation}.
     *
     * @param rootOfCalculation Any node in a scene graph
     * @param child             A direct/indirect child of rootOfCalculation
     * @return A Transformation between coordinates of child and rootOfCalculation
     */
    public static Transform calculateTransformRelativeTo(Node rootOfCalculation, Node child) {
        if (child.getScene() == null) {
            throw new IllegalStateException("Child is not displayed in any scene currently.");
        }
        if (child.getParent() == null) {
            throw new IllegalStateException(
                    "rootOfCalculation is not in the scenegraph between root node and child.");
        }
        if (child == rootOfCalculation) {
            return new Affine();
        }
        Transform parentTransform = calculateTransformRelativeTo(rootOfCalculation, child.getParent());
        return child.getLocalToParentTransform().createConcatenation(parentTransform);
    }

    /**
     * Adds the style sheet (name "style.css" and located in the same package) to the given parent and
     * sets the css-id for the parent
     *
     * @param parent parent that should be setup
     */
    public static void setupView(Parent parent) {
        setupView(parent, "style.css");
    }

    /**
     * Adds the style sheet (located in the same package) to the given parent and sets the css-id for
     * the parent.
     *
     * @param parent     parent that should be setup
     * @param stylesheet stylesheet's name in the package
     */
    public static void setupView(Parent parent, String stylesheet) {
        parent.getStylesheets().add(parent.getClass().getResource(stylesheet).toExternalForm());
        setupClass(parent);
    }

    /**
     * Sets the css-class for the parent.
     *
     * @param parent parent that should be setup
     */
    public static void setupClass(Parent parent) {
        setupClass(parent, parent.getClass().getSimpleName());
    }

    /**
     * @param parent
     * @param clazz
     */
    public static void setupClass(Parent parent, String clazz) {
        parent.getStyleClass().add(clazz);
        LOGGER.debug("Style Class known: " + parent.getClass().getSimpleName());
    }

    /**
     * @param url the url of the website to be shown
     */
    public static void openHelpText(String title, String url) {
        WebView wv = new WebView();
        wv.getEngine().setJavaScriptEnabled(false);
        wv.getEngine().load(url);
        Scene pane = new Scene(wv);
        Stage state = new Stage();
        state.setScene(pane);
        //                pane.getButtonTypes().add(ButtonType.CLOSE);
        state.setAlwaysOnTop(true);
        state.setTitle(title);
        state.setResizable(true);
        state.setOpacity(0.8);
        state.setMinHeight(250);
        state.setMinWidth(250);
        state.show();
    }

    public static void autoFitTable(TableView tableView) {
        for (Object column : tableView.getColumns()) {
            try {
                columnToFitMethod.invoke(tableView.getSkin(), column, -1);
            } catch (IllegalAccessException | InvocationTargetException e) {
                e.printStackTrace();
            }
        }
    }
}
