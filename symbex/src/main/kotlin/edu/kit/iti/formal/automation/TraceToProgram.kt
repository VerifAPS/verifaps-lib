package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.rvt.ASSIGN_SEPARATOR
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.AssignmentStatement
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.util.CodeWriter

class VisualizeTrace(val cex: CounterExample,
                     val lineMap: LineMap,
                     val program: PouExecutable,
                     val stream: CodeWriter) {
    var programVariableToSVar: (VariableDeclaration) -> String = {it.name}

    fun get(k: Int) = get(k - 1, k)
    fun get(kInput: Int, kState: Int) {
        val tsp = TraceStPrinter(stream, lineMap,
                inputValues = cex.states[kInput],
                outputValues = cex.states[kState],
                programVariableToSVar = programVariableToSVar)
        program.accept(tsp)
    }
}

private class TraceStPrinter(sb: CodeWriter,
                             lineMap: LineMap,
                             val inputValues: Map<String, String>,
                             val outputValues: Map<String, String>,
                             val programVariableToSVar: (VariableDeclaration) -> String = { it.name })
    : StructuredTextPrinter(sb) {
    val intSuffx = ".*[$ASSIGN_SEPARATOR](\\d+)$".toRegex()
    val pos2Assign =
            lineMap.map { (a, b) -> b.second to (b.first to a) }
                    .toMap()
    val values = inputValues.mapNotNull { (a, b) ->
        intSuffx.matchEntire(a)?.let { m ->
            m.groupValues[1].toInt() to b
        }
    }.toMap()

    override fun visit(assignmentStatement: AssignmentStatement) {
        super.visit(assignmentStatement)
        val pos = assignmentStatement.startPosition
        pos2Assign[pos]?.let {
            val (k, cnt) = it
            values[cnt]?.let { value ->
                sb.append(" // $k = $value")
            }
        }
    }

    override fun visit(programDeclaration: ProgramDeclaration) {
        super.visit(programDeclaration)
        programDeclaration.scope.forEach {
            val map = if(it.isInput) inputValues else outputValues
            map[programVariableToSVar(it)]?.let { v ->
                sb.println("// ${it.name} = $v")
            }
        }
    }

    override fun print(vd: VariableDeclaration) {
        super.print(vd)
        inputValues[programVariableToSVar(vd)]?.let { v ->
            sb.println("// ${vd.name} = $v")
        }
    }

}