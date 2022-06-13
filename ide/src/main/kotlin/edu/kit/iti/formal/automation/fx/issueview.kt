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
