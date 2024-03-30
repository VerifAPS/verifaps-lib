package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.view.Controller
import javafx.beans.property.BooleanProperty
import javafx.collections.FXCollections
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.geometry.Side
import javafx.scene.chart.Axis
import javafx.scene.chart.CategoryAxis
import javafx.scene.chart.NumberAxis
import javafx.scene.chart.XYChart
import javafx.scene.control.MenuItem
import javafx.scene.input.MouseButton
import javafx.scene.input.MouseEvent
import org.apache.commons.lang3.tuple.ImmutablePair
import org.apache.commons.lang3.tuple.Pair
import kotlin.math.min

/**
 * Controller for a single [TimingDiagramView] that covers all cycles of **one**
 * [ValidIoVariable] in a [ConcreteSpecification].
 *
 * @author Leon Kaucher
 */
class TimingDiagramController : Controller {
    private val activated: BooleanProperty

    /*
   * private void updateAxisExternalPosition() { Transform transformation =
   * ViewUtils.calculateTransformRelativeTo(view.getParent().getParent().getParent(),
   * view.getyAxis()); double yAxisPosition =
   * transformation.transform(view.getyAxis().getLayoutBounds()).getMinY();
   * externalYAxis.layoutYProperty().set(yAxisPosition); }
   */
    override val view: TimingDiagramView<*>
    private val selection: Selection?
    private val ioVariable: ValidIoVariable
    private val concreteSpec: ConcreteSpecification?
    private val commonXAxis: NumberAxis?
    private var lastMouseEvent: MouseEvent? = null


    /**
     * Instantiates a new Timing diagram controller with a number xAxis.
     *
     * @param commonXAxis the common x axis
     * @param externalYAxis the external y axis
     * @param spec the specification
     * @param ioVariable the io variable
     * @param selection the selection that should be updated
     * @param activated property that indicates if the selection should be updated
     */
    constructor(
        commonXAxis: NumberAxis?, externalYAxis: NumberAxis,
        spec: ConcreteSpecification?, ioVariable: ValidIoVariable, selection: Selection?,
        activated: BooleanProperty
    ) {
        this.activated = activated
        this.selection = selection
        this.ioVariable = ioVariable
        this.concreteSpec = spec
        this.commonXAxis = commonXAxis
        val xaxis = NumberAxis(0.0, 0.0, 1.0)
        val yaxis = NumberAxis()
        val view = TimingDiagramView(xaxis, yaxis)
        this.view = view
        val seriesData =
            Plotable.toNumberSeries(spec!!.getColumnByName(ioVariable.name).cells)
        val data = FXCollections.observableArrayList<XYChart.Series<Number?, Number?>?>()
        data.add(seriesData)
        view.data.addAll(data)

        externalYAxis.prefHeightProperty().bind(yaxis.heightProperty())
        externalYAxis.upperBoundProperty().bind(yaxis.upperBoundProperty())
        externalYAxis.lowerBoundProperty().bind(yaxis.lowerBoundProperty())
        xaxis.lowerBoundProperty().bind(commonXAxis!!.lowerBoundProperty())
        xaxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty())
        yaxis.styleClass.add("zeroWidth")

        initCommon()
    }

    /**
     * Instantiates a new Timing diagram controller with a category xAxis.
     *
     * @param commonXAxis the common x axis
     * @param externalYAxis the external y axis
     * @param spec the specification
     * @param ioVariable the io variable
     * @param selection the selection that should be updated
     * @param activated property that indicates if the selection should be updated
     */
    constructor(
        commonXAxis: NumberAxis?, externalYAxis: CategoryAxis,
        spec: ConcreteSpecification?, ioVariable: ValidIoVariable, selection: Selection?,
        activated: BooleanProperty
    ) {
        this.activated = activated
        this.ioVariable = ioVariable
        this.selection = selection
        this.concreteSpec = spec
        this.commonXAxis = commonXAxis
        val xaxis = NumberAxis(0.0, 0.0, 1.0)
        val yaxis = CategoryAxis()
        val view = TimingDiagramView(xaxis, yaxis)
        this.view = view
        val seriesData =
            Plotable.toStringSeries(spec!!.getColumnByName(ioVariable.name).cells)
        val data = FXCollections.observableArrayList<XYChart.Series<Number?, String?>?>()
        data.add(seriesData)
        view.data.addAll(data)

        externalYAxis.prefHeightProperty().bind(yaxis.heightProperty())
        yaxis.isAutoRanging = true
        yaxis.categories = externalYAxis.categories
        xaxis.lowerBoundProperty().bind(commonXAxis!!.lowerBoundProperty())
        xaxis.upperBoundProperty().bind(commonXAxis.upperBoundProperty())

        initCommon()
    }


    /**
     * Create mouse events and context menu entries.
     */
    private fun initCommon() {
        view.setDurations(concreteSpec!!.durations)
        // view.getyAxis().layoutBoundsProperty().addListener(change -> updateAxisExternalPosition());
        view.onMouseClicked = EventHandler { mouseEvent: MouseEvent -> this.onMouseClicked(mouseEvent) }
        val xpositiveZoomItem = MenuItem("Zoom X+")
        xpositiveZoomItem.onAction = EventHandler { actionEvent: ActionEvent -> this.onXPositiveZoom(actionEvent) }
        val xnegativeZoomItem = MenuItem("Zoom X-")
        xnegativeZoomItem.onAction = EventHandler { actionEvent: ActionEvent -> this.onXNegativeZoom(actionEvent) }
        view.contextMenu.items.setAll(xpositiveZoomItem, xnegativeZoomItem)
        val cycleSelectionRectangles = view.cycleSelectionRectangles
        for (i in cycleSelectionRectangles!!.indices) {
            val cycleSelectionRectangle = cycleSelectionRectangles[i]
            val finalCycleIndex = i
            cycleSelectionRectangle!!.onMouseEntered = EventHandler { event: MouseEvent? ->
                if (activated.get()) {
                    cycleSelectionRectangle.opacity = 1.0
                    selection!!.row = concreteSpec.cycleToRowNumber(finalCycleIndex)
                    selection.column = ioVariable.name
                }
            }
            cycleSelectionRectangle.onMouseExited = EventHandler { event: MouseEvent? ->
                if (activated.get()) {
                    cycleSelectionRectangle.opacity = 0.0
                    selection!!.clear()
                }
            }
            cycleSelectionRectangle.onMouseClicked = EventHandler { event: MouseEvent ->
                if (event.button == MouseButton.PRIMARY) {
                    selection!!.fireClickEvent(
                        ioVariable.name,
                        concreteSpec.cycleToRowNumber(finalCycleIndex)
                    )
                }
            }
        }
    }

    private fun onXPositiveZoom(actionEvent: ActionEvent) {
        val interval = commonXAxis!!.upperBound - commonXAxis.lowerBound
        val newInterval = interval / 2
        if (newInterval < 1) {
            return
        }
        val center = commonXAxis.getValueForDisplay(lastMouseEvent!!.x).toDouble()
        var newLowerBound = center - newInterval / 2
        var newUpperBound = center + newInterval / 2
        if (newLowerBound < 0) {
            newUpperBound += -newLowerBound
            newLowerBound = 0.0
        }
        commonXAxis.lowerBound = newLowerBound
        commonXAxis.upperBound = newUpperBound
    }

    private fun onXNegativeZoom(actionEvent: ActionEvent) {
        val interval = commonXAxis!!.upperBound - commonXAxis.lowerBound
        val newInterval = interval * 2
        if (newInterval < 1) {
            return
        }
        val center = commonXAxis.getValueForDisplay(lastMouseEvent!!.x).toDouble()
        var newLowerBound = center - newInterval / 2
        var newUpperBound = center + newInterval / 2
        if (newLowerBound < 0) {
            newUpperBound += -newLowerBound
            newLowerBound = 0.0
        }
        commonXAxis.lowerBound = newLowerBound
        commonXAxis.upperBound = min(newUpperBound, concreteSpec!!.rows!!.size.toDouble())
    }

    private fun onMouseClicked(mouseEvent: MouseEvent) {
        if (mouseEvent.button == MouseButton.SECONDARY) {
            this.lastMouseEvent = mouseEvent
            view.contextMenu.show(view, mouseEvent.screenX, mouseEvent.screenY)
        }
    }

    companion object {
        /*
  All Diagrams are constructed via factory-methods because the NumberAxis is a final class.
   */
        /**
         * Generates an integer timing diagram.
         *
         * @param concreteSpec the concrete specification which should be used to extract the needed
         * information
         * @param specIoVar the variable for which a diagram should be generated
         * @param globalXAxis  global x axis used for all diagrams
         * @param selection selection that should be updated when hovering with mouse
         * @param activated only update selection if true
         * @return A [Pair] which holds a [TimingDiagramController] and a [NumberAxis]
         */
        fun createIntegerTimingDiagram(
            concreteSpec: ConcreteSpecification?, specIoVar: ValidIoVariable, globalXAxis: NumberAxis?,
            selection: Selection?, activated: BooleanProperty
        ): Pair<TimingDiagramController, Axis<*>> {
            val yaxis = NumberAxis(0.0, 10.0, 1.0)
            yaxis.prefWidth = 30.0
            yaxis.side = Side.LEFT
            yaxis.tickLabelFormatter = IntegerTickLabelConverter()
            yaxis.isMinorTickVisible = false
            val timingDiagramController = TimingDiagramController(
                globalXAxis,
                yaxis, concreteSpec, specIoVar, selection, activated
            )
            return ImmutablePair(timingDiagramController, yaxis)
        }

        /**
         * Generates a boolean timing diagram.
         *
         * @param concreteSpec the concrete specification which should be used to extract the needed
         * information
         * @param specIoVar the variable for which a diagram should be generated
         * @param globalXAxis  global x axis used for all diagrams
         * @param selection selection that should be updated when hovering with mouse
         * @param activated only update selection if true
         * @return A [Pair] which holds a [TimingDiagramController] and a [CategoryAxis]
         */
        fun createBoolTimingDiagram(
            concreteSpec: ConcreteSpecification?, specIoVar: ValidIoVariable, globalXAxis: NumberAxis?,
            selection: Selection?, activated: BooleanProperty
        ): Pair<TimingDiagramController, Axis<*>> {
            val categories = FXCollections.observableArrayList<String>()
            categories.addAll("FALSE", "TRUE")
            val boolCategoryAxis = CategoryAxis(categories)
            boolCategoryAxis.prefWidth = 30.0
            boolCategoryAxis.side = Side.LEFT
            boolCategoryAxis.isAutoRanging = true
            val timingDiagramController = TimingDiagramController(
                globalXAxis,
                boolCategoryAxis, concreteSpec, specIoVar, selection, activated
            )
            return ImmutablePair(timingDiagramController, boolCategoryAxis)
        }

        /**
         * Generates an enum timing diagram.
         *
         * @param concreteSpec the concrete specification which should be used to extract the needed
         * information
         * @param specIoVar the variable for which a diagram should be generated
         * @param typeEnum type of the enum this diagram is generated for
         * @param globalXAxis  global x axis used for all diagrams
         * @param selection selection that should be updated when hovering with mouse
         * @param activated only update selection if true
         * @return A [Pair] which holds a [TimingDiagramController] and a [CategoryAxis]
         */
        fun createEnumTimingDiagram(
            concreteSpec: ConcreteSpecification?, specIoVar: ValidIoVariable, typeEnum: TypeEnum?,
            globalXAxis: NumberAxis?, selection: Selection?, activated: BooleanProperty
        ): Pair<TimingDiagramController, Axis<*>> {
            val categories = FXCollections.observableArrayList<String>()
            typeEnum!!.values.stream().map(ValueEnum::valueString).forEach(categories::add)
            val categoryAxis = CategoryAxis(categories)
            categoryAxis.side = Side.LEFT
            categoryAxis.prefWidth = 30.0
            categoryAxis.isAutoRanging = true
            val timingDiagramController = TimingDiagramController(
                globalXAxis,
                categoryAxis, concreteSpec, specIoVar, selection, activated
            )
            return ImmutablePair(timingDiagramController, categoryAxis)
        }
    }
}
