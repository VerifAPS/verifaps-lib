/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
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
                { valueEnum: ValueEnum? -> valueEnum!!.type.values.indexOf(valueEnum) },
            )
            dataSeries.data.add(XYChart.Data(i, cellAsNumber))
        }
        return dataSeries
    }
}