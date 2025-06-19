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
package edu.kit.iti.formal.automation.fx

import edu.kit.iti.formal.automation.analysis.ReporterMessage
import javafx.collections.FXCollections
import tornadofx.View
import tornadofx.column
import tornadofx.tableview

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/21/21)
 */
class Issues : View("Issues") {
    val issues = FXCollections.observableArrayList<Problem>()

    override val root = tableview(issues) {
        column("File", Problem::sourceName)
        column("Message", Problem::message)
    }
}

typealias Problem = ReporterMessage

interface ProblemService {
    fun clearProblems(identity: Any)
    fun announceProblems(identity: Any, problems: Iterable<Problem>)
    fun registerListener(listener: () -> Unit)
}