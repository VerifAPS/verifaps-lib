package edu.kit.iti.formal.stvs.view.spec.timingdiagram

import edu.kit.iti.formal.stvs.model.common.*
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.view.*
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramController
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.TimingDiagramView
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.VerticalResizeContainerController
import javafx.beans.Observable
import javafx.beans.property.*
import javafx.event.EventHandler
import javafx.scene.chart.Axis
import javafx.scene.control.*
import javafx.scene.input.*
import javafx.scene.layout.AnchorPane
import tornadofx.getValue
import tornadofx.setValue
import java.util.*
import java.util.function.Consumer
import kotlin.math.max

/**
 * Represents the controller for the collection of multiple timing diagrams.
 *
 * @author Leon Kaucher
 */
class TimingDiagramCollectionController(
    concreteSpec: ConcreteSpecification?,
    private val selection: Selection?
) : Controller {
    private val totalCycleCount = concreteSpec!!.rows.size
    private val dragState = XAxisDragState()
    override val view: TimingDiagramCollectionView = TimingDiagramCollectionView()
    private val visibleRange: DoubleProperty = SimpleDoubleProperty()

    val activatedProperty: BooleanProperty = SimpleBooleanProperty(true)
    var activated by activatedProperty

    /**
     * Creates the controller for a [TimingDiagramCollectionView]. This controller uses a given
     * [ConcreteSpecification] to generate a [TimingDiagramController] for each
     * [ValidIoVariable] in the specification.
     *
     * @param concreteSpec the concrete specification that should be displayed
     * @param selection the selection that should be used for selecting cycles
     */
    init {
        view.onMouseDraggedProperty().value = EventHandler { event: MouseEvent -> this.mouseDraggedHandler(event) }
        view.onMousePressedProperty().value = EventHandler { event: MouseEvent -> this.mousePressedHandler(event) }

        view.outdatedMessage.visibleProperty().bind(activatedProperty.not())
        view.outdatedMessage.managedProperty().bind(activatedProperty.not())

        concreteSpec!!.columnHeaders.forEach(Consumer { validIoVariable: ValidIoVariable ->
            createTimingDiagram(concreteSpec, validIoVariable)
        })
        view.xaxis.upperBound = concreteSpec.rows.size.toDouble()
        initxScrollbar()
    }

    /**
     * Generates a [TimingDiagramController] for a given [ValidIoVariable]. The method
     * adds multiple views to the [view][TimingDiagramCollectionView] of this controller:
     *
     *  * A [TimingDiagramView] wrapped in a
     * [edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer.VerticalResizeContainerView]
     * will be added to [TimingDiagramCollectionView.diagramContainer]
     *  * A [Label] (title of the [ValidIoVariable]) will be added to
     * [TimingDiagramCollectionView.labelContainer]
     *  * A [Axis] will be added to the [TimingDiagramCollectionView.yaxisContainer]
     *
     *
     * @param concreteSpec the concrete specification which should be used to extract the needed
     * information
     * @param validIoVariable the variable for which a diagram should be generated
     */
    private fun createTimingDiagram(
        concreteSpec: ConcreteSpecification?,
        validIoVariable: ValidIoVariable
    ) {
        val diagramAxisPair = validIoVariable.validType.match(
            {
                TimingDiagramController.createIntegerTimingDiagram(
                    concreteSpec, validIoVariable,
                    view.xaxis, selection, activatedProperty
                )
            },
            {
                TimingDiagramController.createBoolTimingDiagram(
                    concreteSpec, validIoVariable,
                    view.xaxis, selection, activatedProperty
                )
            },
            { e: TypeEnum? ->
                TimingDiagramController.createEnumTimingDiagram(
                    concreteSpec, validIoVariable, e,
                    view.xaxis, selection, activatedProperty
                )
            })!!
        val timingDiagramView = diagramAxisPair.first.view

        if (concreteSpec!!.isCounterExample) {
            timingDiagramView.styleClass.add("counterexample")
        }
        val externalYAxis = diagramAxisPair.second
        val verticalResizeContainerController =
            VerticalResizeContainerController(timingDiagramView)

        view.diagramContainer.children.add(verticalResizeContainerController.view)
        view.getyAxisContainer().children.add(externalYAxis)
        timingDiagramView.getyAxis().layoutBoundsProperty()
            .addListener { change: Observable? -> updateAxisExternalPosition(timingDiagramView, externalYAxis) }
        verticalResizeContainerController.view.layoutYProperty()
            .addListener { change: Observable? -> updateAxisExternalPosition(timingDiagramView, externalYAxis) }
        AnchorPane.setRightAnchor(externalYAxis, 0.0)

        val label = Label(validIoVariable.name)
        label.styleClass.add(validIoVariable.category.name.lowercase(Locale.getDefault()))
        view.labelContainer.children.add(label)
        // Ensures that labels are always centered vertically relative to their diagram
        label.layoutYProperty().bind(
            externalYAxis.layoutYProperty()
                .add(externalYAxis.heightProperty().divide(2)).subtract(label.heightProperty().divide(2))
        )
    }

    /**
     * Ensures that the scrollbar below the xAxis can only be used within the range of the shown data
     * and that the scrollbar position and shown range are always synchronized.
     */
    private fun initxScrollbar() {
        val scrollBar = view.xscrollBar
        val globalxAxis = view.xaxis
        scrollBar.min = 0.0
        visibleRange.bind(globalxAxis.upperBoundProperty().subtract(globalxAxis.lowerBoundProperty()))
        scrollBar.maxProperty().bind(visibleRange.multiply(-1).add(totalCycleCount))

        globalxAxis.lowerBoundProperty().addListener { change: Observable? ->
            scrollBar.value = globalxAxis.lowerBound
        }

        // I don't know, why it need to be divided by 2 but it seems to work very good this way
        scrollBar.visibleAmountProperty().bind(visibleRange.divide(2))

        scrollBar.valueProperty().addListener { change: Observable? ->
            globalxAxis.upperBound = scrollBar.value + visibleRange.get()
            globalxAxis.lowerBound = scrollBar.value
        }
    }

    /**
     * This method calculates the position of an y [Axis] embedded in a diagram relative to the
     * [TimingDiagramCollectionView.diagramContainer] and updates the position of the external
     * axis.
     *
     * @param timingDiagramView Timing Diagram which holds the y Axis
     * @param externalYAxis externalYAxis that should be repositioned
     */
    private fun updateAxisExternalPosition(timingDiagramView: TimingDiagramView<*>?, externalYAxis: Axis<*>) {
        val transformation = ViewUtils.calculateTransformRelativeTo(
            view.diagramContainer,
            timingDiagramView!!.getyAxis()
        )
        val yaxisPosition =
            transformation.transform(timingDiagramView.getyAxis().layoutBounds).minY
        externalYAxis.layoutYProperty().set(yaxisPosition)
    }

    /**
     * Handles drag events on xAxis.
     *
     * @param event mouse event
     */
    private fun mouseDraggedHandler(event: MouseEvent) {
        val point2D = view.sceneToLocal(event.sceneX, event.screenY)
        val newXPosition = point2D.x
        val delta = newXPosition - dragState.startXPosition
        var deltaAsAxis = delta * dragState.screenDistanceToAxisRatio
        if (dragState.startLowerBound - deltaAsAxis < 0) {
            deltaAsAxis = dragState.startLowerBound
        }
        val xaxis = view.xaxis
        xaxis.lowerBound = max(dragState.startLowerBound - deltaAsAxis, 0.0)
        xaxis.upperBound = max(dragState.startUpperBound - deltaAsAxis, visibleRange.get())
    }

    /**
     * Handles press events on xAxis.
     *
     * @param event mouse event
     */
    private fun mousePressedHandler(event: MouseEvent) {
        val point2D = view.sceneToLocal(event.sceneX, event.screenY)
        val xaxis = view.xaxis
        val displayForAxis = xaxis.getValueForDisplay(point2D.x).toDouble()
        val displayForAxisPlus100 = xaxis.getValueForDisplay(point2D.x + 100).toDouble()
        /*
     * Calculates Ratio between pixel and axis units by taking to different points on the axis and
     * dividing them by the screen distance
     */
        dragState.screenDistanceToAxisRatio = (displayForAxisPlus100 - displayForAxis) / 100
        dragState.startXPosition = point2D.x
        dragState.startLowerBound = xaxis.lowerBound
        dragState.startUpperBound = xaxis.upperBound
        println(point2D)
    }

    private class XAxisDragState {
        var startXPosition: Double = 0.0
        var startLowerBound: Double = 0.0
        var startUpperBound: Double = 0.0
        var screenDistanceToAxisRatio: Double = 0.0
    }
}
