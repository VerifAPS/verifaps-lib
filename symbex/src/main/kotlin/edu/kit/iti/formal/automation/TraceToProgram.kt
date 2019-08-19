package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.AssignmentStatement
import edu.kit.iti.formal.automation.st.ast.Position
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.util.CodeWriter

class VisualizeTrace(val cex: CounterExample,
                     val lineMap: LineMap,
                     val program: PouExecutable) {

    fun get(k: Int): String {
        val stream = CodeWriter()
        val tsp = TraceStPrinter(stream, lineMap, cex.states[k])
        program.accept(tsp)
        return stream.stream.toString()
    }
}

private class TraceStPrinter(sb: CodeWriter,
                             lineMap: LineMap,
                             values: Map<String, String>)
    : StructuredTextPrinter(sb) {
    val inv =
            lineMap.map { (a, b) -> b.second to (b.first to a) }
                    .toMap()
    val intSuffx = "^.*_(\\d+)$".toRegex()
    val values = values.mapNotNull { (a, b) ->
        intSuffx.matchEntire(a)?.let { m ->
            m.groupValues[1].toInt() to b
        }
    }.toMap()

    override fun visit(assignmentStatement: AssignmentStatement) {
        super.visit(assignmentStatement)
        val pos = assignmentStatement.startPosition
        inv[pos]?.let {
            val (k, cnt) = it
            values[cnt]?.let { value ->
                sb.append(" // $k = $value")
            }
        }
    }
}