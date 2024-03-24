package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.scene.layout.AnchorPane
import javafx.scene.layout.VBox
import javafx.scene.paint.Color
import javafx.scene.shape.Rectangle

/**
 * Creates a Container for resizing through a horizontal bar.
 *
 * @author Leon Kaucher
 */
class VerticalResizeContainerView : AnchorPane() {
    val container: VBox = VBox()
    val content: AnchorPane = AnchorPane()
    val contentContainer: VBox = VBox()
    val dragLine: Rectangle = Rectangle(10.0, 10.0, Color.BEIGE)

    /**
     * Creates an instance of this container class.
     */
    init {
        children.add(container)
        container.children.addAll(contentContainer)
        contentContainer.children.addAll(content, dragLine)
        setLeftAnchor(container, 0.0)
        setRightAnchor(container, 0.0)
        setTopAnchor(container, 0.0)
        dragLine.widthProperty().bind(container.widthProperty())
        // AnchorPane.setBottomAnchor(dragLine, 0.0);
        ViewUtils.setupView(this, "resizeContainer.css")

        styleClass.add("resizeContainer")
        dragLine.styleClass.add("dragLine")
    }
}
