package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.view.*
import javafx.application.Platform
import javafx.beans.property.*
import javafx.event.EventHandler
import javafx.scene.Node
import javafx.scene.input.*
import javafx.scene.layout.AnchorPane

/**
 * Controller for [VerticalResizeContainerView].
 *
 * @author Leon Kaucher
 */
class VerticalResizeContainerController(wrap: Node?) : Controller {
    override var view: VerticalResizeContainerView = VerticalResizeContainerView()
    private val mouseYStart: DoubleProperty = SimpleDoubleProperty(0.0)
    private val cacheSize: DoubleProperty = SimpleDoubleProperty(0.0)

    /**
     * Creates a simple wrapper that enables one to vertically resize the given Node.
     *
     * @param wrap Node that should be wrapped
     */
    init {
        view.content.children.add(wrap)
        AnchorPane.setLeftAnchor(wrap, 0.0)
        AnchorPane.setRightAnchor(wrap, 0.0)
        AnchorPane.setTopAnchor(wrap, 0.0)
        AnchorPane.setBottomAnchor(wrap, 0.0)
        view.dragLine.onMousePressed = EventHandler { event: MouseEvent ->
            mouseYStart.value = event.screenY
            cacheSize.value = view.content.height
            view.contentContainer.prefHeight = view.content.height
        }
        view.dragLine.onMouseDragged = EventHandler { event: MouseEvent ->
            val newSize = cacheSize.get() + (event.screenY - mouseYStart.get())
            if (newSize >= cacheSize.get()) {
                view.contentContainer.prefHeight = newSize
            }
            view.content.prefHeight = newSize
        }
        view.dragLine.onMouseReleased = EventHandler { event: MouseEvent ->
            println("release")
            val newSize = cacheSize.get() + (event.screenY - mouseYStart.get())
            view.contentContainer.prefHeight = newSize
            view.content.prefHeight = newSize
            Platform.runLater {
                view.parent.parent.parent.parent.parent
                    .parent.requestLayout()
            }
        }
    }
}
