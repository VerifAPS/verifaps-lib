package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.rvt.ASSIGN_SEPARATOR
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto

class VisualizeTrace(val cex: CounterExample,
                     val lineMap: LineMap,
                     val program: PouExecutable,
                     val stream: CodeWriter) {
    var programVariableToSVar: (String) -> String = { it }

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
                             val lineMap: LineMap,
                             val inputValues: Map<String, String>,
                             val outputValues: Map<String, String>,
                             val programVariableToSVar: (String) -> String)
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

    private fun printBranchCondition(ifStatement: Top, branch: Top) {
        lineMap.branchMap.entries.find { (_, p) ->
            val (p1,p2) = p
            p1 == ifStatement.startPosition && branch.startPosition == p2
        }?.let {
            //as branch conditions are defined on the old state + input, we need to lookup in the prev. state
            sb.print(" // ${it.key} = ${inputValues[programVariableToSVar(it.key)]}")
        }
    }

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
            map[programVariableToSVar(it.name)]?.let { v ->
                sb.println("// ${it.name} = $v")
            }
        }
    }

    override fun print(vd: VariableDeclaration) {
        super.print(vd)
        inputValues[programVariableToSVar(vd.name)]?.let { v ->
            sb.println("// ${vd.name} = $v")
        }
    }

    override fun visit(caseStatement: CaseStatement) {
        sb.nl().printf("CASE ")
        caseStatement.expression.accept(this)
        sb.printf(" OF ").increaseIndent()

        for (c in caseStatement.cases) {
            sb.nl()
            c.conditions.joinInto(sb) { it.accept(this) }
            sb.printf(":")
            printBranchCondition(caseStatement, c)
            sb.block() {
                c.statements.accept(this@TraceStPrinter)
            }
            sb.nl()
        }

        if (caseStatement.elseCase.isNotEmpty()) {
            sb.nl().printf("ELSE ")
            printBranchCondition(caseStatement, caseStatement.elseCase)
            caseStatement.elseCase.accept(this)
        }

        sb.nl().decreaseIndent().appendIdent().printf("END_CASE;")

    }

    override fun visit(ifStatement: IfStatement) {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            sb.nl()

            if (i == 0)
                sb.printf("IF ")
            else
                sb.printf("ELSIF ")

            ifStatement.conditionalBranches[i].condition.accept(this)

            sb.printf(" THEN").increaseIndent()

            printBranchCondition(ifStatement, ifStatement.conditionalBranches[i])

            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.decreaseIndent()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.nl().printf("ELSE").increaseIndent()
            printBranchCondition(ifStatement, ifStatement.elseBranch)
            ifStatement.elseBranch.accept(this)
            sb.decreaseIndent()
        }
        sb.nl().printf("END_IF")
    }
}