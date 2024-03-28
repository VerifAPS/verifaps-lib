package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.model.expressions.ValueEnum
import edu.kit.iti.formal.stvs.model.table.ConcreteCell
import javafx.scene.chart.XYChart

/**
 * Converts lists of [ConcreteCells][ConcreteCell] to [javafx.scene.chart.XYChart.Series]
 *
 * @author Leon Kaucher
 */
object Plotable {
    /**
     * Converts a list of concrete cells to a string series.
     * This method is used to generate category chart series.
     * It simply converts every data point into its string representation.
     *
     * @param concreteCells cells to convert
     * @return converted series
     */
    fun toStringSeries(concreteCells: List<ConcreteCell>?): XYChart.Series<Number?, String?> {
        val dataSeries = XYChart.Series<Number?, String?>()
        for (i in concreteCells!!.indices) {
            val cellAsString = concreteCells[i].value.valueString
            dataSeries.data.add(XYChart.Data(i, cellAsString))
        }
        return dataSeries
    }

    /**
     * Converts a list of concrete cells to a number series.
     * This method is used to generate number chart series.
     * It converts the cells to numbers depending on their type.
     * @param concreteCells cells to convert
     * @return converted series
     */
    fun toNumberSeries(concreteCells: List<ConcreteCell>?): XYChart.Series<Number?, Number?> {
        val dataSeries = XYChart.Series<Number?, Number?>()
        for (i in concreteCells!!.indices) {
            val cellAsNumber: Number? = concreteCells[i].value!!.match(
                { integer: Int -> integer },
                { bool: Boolean -> if (bool) 1 else 0 },
                { valueEnum: ValueEnum? -> valueEnum!!.type.values.indexOf(valueEnum) }
            )
            dataSeries.data.add(XYChart.Data(i, cellAsNumber))
        }
        return dataSeries
    }
}
