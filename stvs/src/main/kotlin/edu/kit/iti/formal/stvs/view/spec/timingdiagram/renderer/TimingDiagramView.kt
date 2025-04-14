package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.model.table.ConcreteDuration
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.application.Platform
import javafx.beans.Observable
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import javafx.scene.chart.Axis
import javafx.scene.chart.NumberAxis
import javafx.scene.chart.XYChart
import javafx.scene.control.ContextMenu
import javafx.scene.control.Tooltip
import javafx.scene.layout.Pane
import javafx.scene.shape.Line
import javafx.scene.shape.Rectangle
import java.util.function.Consumer
import java.util.stream.Collectors

/**
 * A TimingDiagram which displays a series of values as a line chart.
 *
 * @author Leon Kaucher
 */
class TimingDiagramView<A>(private val xaxis: NumberAxis, private val yaxis: Axis<A>) :
    XYChart<Number?, A>(xaxis, yaxis) {
    private val horizontalLines: ObservableList<Line> = FXCollections.observableArrayList()
    private val verticalLines: ObservableList<Line> = FXCollections.observableArrayList()
    private val durationLines: ObservableList<Line> = FXCollections.observableArrayList()
    val cycleSelectionRectangles: ObservableList<Rectangle> = FXCollections.observableArrayList()
    private var durations: List<ConcreteDuration> = ArrayList()

    private val dataPane = Pane()
    private val cycleSelectionPane = Pane()
    private val durationLinesPane = Pane()

    val contextMenu: ContextMenu = ContextMenu()

    /**
     * Instantiates a new Timing diagram view.
     *
     * @param xaxis the x axis
     * @param yaxis the y axis
     */
    init {
        prefHeight = 80.0
        plotChildren.addAll(cycleSelectionPane, durationLinesPane, dataPane)
        ViewUtils.setupView(this)

        val seriesObservableList = FXCollections.observableArrayList<Series<Number?, A>>()
        data = seriesObservableList
        seriesObservableList.addListener { _: Observable? ->
            Platform.runLater { this@TimingDiagramView.requestRelayout() }
        }
    }

    private fun requestRelayout() {
        requestLayout()
        requestChartLayout()
    }

    /**
     * **copied from super and modified**
     *
     *
     * Called when a data item has been added to a series. This is where implementations of XYChart
     * can create/add new nodes to getPlotChildren to represent this data item.
     *
     *
     * The following nodes are created here:
     *
     *  * Horizontal lines for values
     *  * Vertical lines to connect values
     *  * Rectangles to perform selections and highlighting
     *  * Tooltips to show the value of a specific item
     *
     *
     * @param series The series the data item was added to
     * @param itemIndex The index of the new item within the series
     * @param item The new data item that was added
     */
    override fun dataItemAdded(series: Series<Number?, A>, itemIndex: Int, item: Data<Number?, A>) {
        val horizontalLine = Line()
        horizontalLine.styleClass.add("valueLine")
        dataPane.children.add(horizontalLine)
        dataPane.isMouseTransparent = true
        durationLinesPane.isMouseTransparent = true
        horizontalLines.add(horizontalLine)
        val cycleSelectionRectangle = Rectangle()
        val tooltip = Tooltip(item.yValue.toString())
        Tooltip.install(cycleSelectionRectangle, tooltip)
        cycleSelectionRectangle.styleClass.add("cycleSelectionRectangle")
        cycleSelectionRectangle.opacity = 0.0
        cycleSelectionRectangles.add(cycleSelectionRectangle)
        cycleSelectionPane.children.add(cycleSelectionRectangle)
        if (itemIndex > 0) {
            val verticalLine = Line()
            verticalLine.styleClass.add("valueLine")
            dataPane.children.add(verticalLine)
            verticalLines.add(verticalLine)
            // updateYRange();
        }
    }

    /**
     * **copied from super and modified.**
     *
     *
     * removes an item from the chart
     *
     * @param item The item that has been removed from the series
     * @param series The series the item was removed from
     */
    override fun dataItemRemoved(item: Data<Number?, A>, series: Series<Number?, A>) {
        removeDataItemFromDisplay(series, item)
        dataPane.children.remove(horizontalLines.removeAt(0))
        cycleSelectionPane.children.remove(cycleSelectionRectangles.removeAt(0))
        if (series.data.size > 0) {
            dataPane.children.remove(verticalLines.removeAt(0))
        }
    }

    /**
     * **copied from super.**
     *
     *
     * Called when a data item has changed, ie its xValue, yValue or extraValue has changed.
     *
     * @param item The data item who was changed
     */
    override fun dataItemChanged(item: Data<Number?, A>?) {
        layoutPlotChildren()
    }

    /**
     * **copied from super and modified**
     *
     *
     * A series has been added to the charts data model. This simply calls
     * [TimingDiagramView.dataItemAdded] for each entry in the series
     *
     * @param series The series that has been added
     * @param seriesIndex The index of the new series
     */
    override fun seriesAdded(series: Series<Number?, A>, seriesIndex: Int) {
        for (i in series.data.indices) {
            dataItemAdded(series, i, series.data[i])
        }
    }

    /**
     * **copied from super and modified.**
     *
     *
     * This simply calls [TimingDiagramView.dataItemRemoved]
     * for each entry in the
     * series
     *
     * @param series The series that has been removed
     */
    override fun seriesRemoved(series: Series<Number?, A>) {
        for (i in series.data.indices) {
            dataItemRemoved(series.data[i], series)
        }
    }

    /**
     * **copied from super and modified.**
     *
     *
     * Called to update and layout the plot children.
     */
    override fun layoutPlotChildren() {
        data.forEach(Consumer { series: Series<Number?, A?> ->
            val cyclesData = series.data
            for (i in cyclesData.indices) {
                val horizontalLine = horizontalLines[i]
                horizontalLine.startX = xAxis.getDisplayPosition(cyclesData[i].xValue)
                horizontalLine.endX = xAxis.getDisplayPosition(cyclesData[i].xValue!!.toInt() + 1)
                horizontalLine.startY = yAxis.getDisplayPosition(cyclesData[i].yValue)
                horizontalLine.endY = yAxis.getDisplayPosition(cyclesData[i].yValue)
                if (i < cyclesData.size - 1) {
                    val verticalLine = verticalLines[i]
                    verticalLine.startX = xAxis.getDisplayPosition(cyclesData[i].xValue!!.toInt() + 1)
                    verticalLine.endX = xAxis.getDisplayPosition(cyclesData[i].xValue!!.toInt() + 1)
                    verticalLine.startY = yAxis.getDisplayPosition(cyclesData[i].yValue)
                    verticalLine.endY = yAxis.getDisplayPosition(cyclesData[i + 1].yValue)
                }

                val cycleSelectionRectangle = cycleSelectionRectangles[i]
                cycleSelectionRectangle.x = xAxis.getDisplayPosition(cyclesData[i].xValue)
                cycleSelectionRectangle.width = (xAxis.getDisplayPosition(cyclesData[i].xValue!!.toInt() + 1)
                        - xAxis.getDisplayPosition(cyclesData[i].xValue))
                cycleSelectionRectangle.height = yAxis.height
            }
            for (i in durations.indices) {
                val line = durationLines[i]
                val duration = durations[i]
                line.startX = getxAxis().getDisplayPosition(duration.endCycle)
                line.endX = getxAxis().getDisplayPosition(duration.endCycle)
                line.endY = yAxis.height
            }
        })
    }

    fun getxAxis(): NumberAxis {
        return xaxis
    }

    fun getyAxis(): Axis<A> {
        return yaxis
    }

    /**
     * Sets durations. This updates the lines that indicates a new row in the specification.
     *
     * @param durations the durations
     */
    fun setDurations(durations: List<ConcreteDuration>) {
        this.durations = durations
        durationLines.setAll(durations.stream().map { i: ConcreteDuration? ->
            val line = Line()
            line.styleClass.add("durationLine")
            durationLinesPane.children.add(line)
            line.startY = 0.0
            line
        }.collect(Collectors.toList()))
    }
}
