package edu.kit.iti.formal.stvs.view

import javafx.scene.Node
import javafx.scene.Parent
import javafx.scene.Scene
import javafx.scene.control.TableView
import javafx.scene.transform.Affine
import javafx.scene.transform.Transform
import javafx.scene.web.WebView
import javafx.stage.Stage
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.lang.reflect.InvocationTargetException
import java.lang.reflect.Method

/**
 * Provides static methods for view operations.
 *
 * @author Benjamin Alt
 */
object ViewUtils {
    val LOGGER: Logger = LoggerFactory.getLogger(ViewUtils::class.java)

    //hack for getting the auto resizing
    //see https://stackoverflow.com/questions/23284437/javafx-tablecolumn-resize-to-fit-cell-content
    private val columnToFitMethod: Method? = null


    /**
     * Calculates the [Transformation][Transform] from children node coordinates to
     * parent node coordinates.
     *
     *
     * `child` must be a direct or indirect child of `rootOfCalculation`.
     *
     * @param rootOfCalculation Any node in a scene graph
     * @param child             A direct/indirect child of rootOfCalculation
     * @return A Transformation between coordinates of child and rootOfCalculation
     */
    fun calculateTransformRelativeTo(rootOfCalculation: Node?, child: Node?): Transform {
        checkNotNull(child!!.scene) { "Child is not displayed in any scene currently." }
        checkNotNull(child.parent) { "rootOfCalculation is not in the scenegraph between root node and child." }
        if (child === rootOfCalculation) {
            return Affine()
        }
        val parentTransform = calculateTransformRelativeTo(rootOfCalculation, child.parent)
        return child.localToParentTransform.createConcatenation(parentTransform)
    }

    /**
     * Adds the style sheet (located in the same package) to the given parent and sets the css-id for
     * the parent.
     *
     * @param parent     parent that should be setup
     * @param stylesheet stylesheet's name in the package
     */
    @JvmOverloads
    fun setupView(parent: Parent, stylesheet: String? = "style.css") {
        parent.stylesheets.add(parent.javaClass.getResource(stylesheet).toExternalForm())
        setupClass(parent)
    }

    /**
     * Sets the css-class for the parent.
     *
     * @param parent parent that should be setup
     */
    @JvmOverloads
    fun setupClass(parent: Parent, clazz: String? = parent.javaClass.simpleName) {
        parent.styleClass.add(clazz)
        LOGGER.debug("Style Class known: " + parent.javaClass.simpleName)
    }

    /**
     * @param url the url of the website to be shown
     */
    fun openHelpText(title: String?, url: String?) {
        val wv = WebView()
        wv.engine.isJavaScriptEnabled = false
        wv.engine.load(url)
        val pane = Scene(wv)
        val state = Stage()
        state.scene = pane
        //                pane.getButtonTypes().add(ButtonType.CLOSE);
        state.isAlwaysOnTop = true
        state.title = title
        state.isResizable = true
        state.opacity = 0.8
        state.minHeight = 250.0
        state.minWidth = 250.0
        state.show()
    }

    fun autoFitTable(tableView: TableView<*>) {
        return // TODO find a modern way for autofit columns
        for (column in tableView.columns) {
            try {
                columnToFitMethod!!.invoke(tableView.skin, column, -1)
            } catch (e: IllegalAccessException) {
                e.printStackTrace()
            } catch (e: InvocationTargetException) {
                e.printStackTrace()
            }
        }
    }
}
