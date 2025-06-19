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
package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.rvt.ASSIGN_SEPARATOR
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.smv.SMVPrinter
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto
import kotlinx.html.*
import kotlinx.html.stream.appendHTML
import java.io.Writer

const val OKMARK = '✔' // ✔
const val ERRMARK = '✘'
const val QMARK = '❓'

class CounterExamplePrinterWithProgramHtml(
    val automaton: TestTableAutomaton,
    val testTable: GeneralizedTestTable,
    val cex: CounterExample,
    val lineMap: LineMap,
    val program: PouExecutable,
    val stream: Writer,
    val name: String,
) {

    fun print(k: Int) {
        stream.appendHTML(true).html {
            head {
                meta(charset = "utf-8")
                title("Iteration $k")
                style {
                    unsafe {
                        +"""
                            body { font-family: sans-serif; }
                            .keyword {color:navy;}
                            .literal {color:darkorange;}                            
                            .comment {color:black;background:rgba(0,0,255,.2); font-size: 80%; padding: 2pt;}
                           
                            .head { text-align: center; }
                   .cycle {
                        display:flex;
                    }
                    
                    .left {
                        width: 50%;
                    }
                    
                    .smv {
                        white-space: pre;
                        font-family: monospace;
                        color:#888;
                    }
                    .code {
                      text-wrap-mode: nowrap;
                      white-space: pre;
                      width: 50%;
                      font-family: monospace;
                      background: #fff;
                    }
                    
                    .right {
                        width: 50%;                  
                    }
                        """.trimIndent()
                    }
                }
            }
            body {
                div("head") {
                    a("$name.${k - 1}.html") { +" ← Prev" }
                    +" Current: $k "
                    a("$name.${k + 1}.html") { +"Next →" }
                }
                div("cycle") {
                    div("left") {
                        h2 { +"Code" }
                        div("code") {
                            val sw = object : CodeWriter() {
                                override fun comment(format: String, vararg args: Any) {
                                    write("<span class=\"comment\">")
                                    super.comment(format, *args)
                                    write("</span>")
                                }

                                override fun keyword(keyword: String): CodeWriter {
                                    write("<span class=\"keyword\">")
                                    super.keyword(keyword)
                                    write("</span>")
                                    return this
                                }
                            }
                            val vt = VisualizeTraceHtml(cex, lineMap, program, sw).also { vt ->
                                vt.programVariableToSVar = { "code$.$it" }
                            }
                            vt.get(k, k + 1)
                            unsafe { +sw.stream.toString() }
                        }
                    }
                    div("right") {
                        h2 { +"Table" }
                        div("table") {
                            printAssertions(k)
                        }
                    }
                }
            }
        }
    }

    private fun DIV.printAssertions(k: Int) {
        printVariables(k)
    }

    private fun DIV.printVariables(k: Int) {
        ul {
            for (row in testTable.region.flat()) {
                val activateStates = isRowActive(k, row)
                val rowActive = if (activateStates.isNotEmpty()) OKMARK else ERRMARK
                val prfx = "_${testTable.name}."
                val assumption = prfx + row.defInput.name
                val assertion = prfx + row.defOutput.name
                val fwd = prfx + row.defForward.name

                val times = activateStates.joinToString(", ") { it.toString() }

                li {
                    unsafe {
                        +(
                            "$rowActive Row ${row.id} ${boolForHuman(
                                k,
                                assumption,
                            )} --> ${boolForHuman(k, assertion)}:" +
                                " ${boolForHuman(k, fwd)} (Time: $times)"
                            )
                    }
                    if (activateStates.isNotEmpty()) {
                        br
                        +"Assumptions"
                        br
                        ul {
                            for (v in row.inputExpr.keys) {
                                li {
                                    val va = "_${testTable.name}." + row.defInput.name + "_" + v
                                    +"$v: ${boolForHuman(k, va)}"
                                    br
                                    span("smv") { +SMVPrinter.toString(row.inputExpr[v]!!) }
                                }
                            }
                        }
                        br
                        +"Assertions"
                        br
                        ul {
                            for (v in row.outputExpr.keys) {
                                li {
                                    val va = "_${testTable.name}." + row.defOutput.name + "_" + v
                                    +"$va: ${boolForHuman(k, va)}"
                                    br
                                    span("smv") { +SMVPrinter.toString(row.outputExpr[v]!!) }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private fun boolForHuman(k: Int, n: String): Char {
        val v = cex[k, n]
        val m = when (v) {
            "TRUE" -> OKMARK
            "FALSE" -> ERRMARK
            else -> QMARK
        }
        return m
    }

    private fun isRowActive(k: Int, it: TableRow): List<Int> = automaton.getStates(it)
        ?.filter { rs ->
            cex[k, "_${testTable.name}.${rs.name}"] == "TRUE"
        }
        ?.map { it.time }
        ?: listOf()
}

class VisualizeTraceHtml(
    val cex: CounterExample,
    val lineMap: LineMap,
    val program: PouExecutable,
    val stream: CodeWriter,
) {
    var programVariableToSVar: (String) -> String = { it }

    fun get(k: Int) = get(k - 1, k)
    fun get(kInput: Int, kState: Int) {
        val tsp = TraceStPrinter(
            stream,
            lineMap,
            inputValues = cex.states[kInput],
            outputValues = cex.states[kState],
            programVariableToSVar = programVariableToSVar,
        )
        program.accept(tsp)
    }
}

private class TraceStPrinter(
    sb: CodeWriter,
    val lineMap: LineMap,
    val inputValues: Map<String, String>,
    val outputValues: Map<String, String>,
    val programVariableToSVar: (String) -> String,
) : StructuredTextPrinter(sb) {
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
            val (p1, p2) = p
            p1 == ifStatement.startPosition && branch.startPosition == p2
        }?.let {
            // as branch conditions are defined on the old state + input, we need to lookup in the prev. state
            sb.comment(" // ${it.key} = ${inputValues[programVariableToSVar(it.key)]}")
        }
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        super.visit(assignmentStatement)
        val pos = assignmentStatement.startPosition
        pos2Assign[pos]?.let {
            val (k, cnt) = it
            values[cnt]?.let { value ->
                sb.comment(" // $k = $value")
            }
        }
    }

    override fun visit(programDeclaration: ProgramDeclaration) {
        super.visit(programDeclaration)
        programDeclaration.scope.forEach {
            val map = if (it.isInput) inputValues else outputValues
            map[programVariableToSVar(it.name)]?.let { v ->
                sb.comment("// ${it.name} = $v\n")
            }
        }
    }

    override fun print(vd: VariableDeclaration) {
        super.print(vd)
        inputValues[programVariableToSVar(vd.name)]?.let { v ->
            sb.comment("// ${vd.name} = $v\n")
        }
    }

    override fun visit(caseStatement: CaseStatement) {
        sb.nl().keyword("CASE").space()
        caseStatement.expression.accept(this)
        sb.space().keyword("OF").increaseIndent()

        for (c in caseStatement.cases) {
            sb.nl()
            c.conditions.joinInto(sb) { it.accept(this) }
            sb.printf(":")
            printBranchCondition(caseStatement, c)
            sb.block {
                c.statements.accept(this@TraceStPrinter)
            }
            sb.nl()
        }

        if (caseStatement.elseCase.isNotEmpty()) {
            sb.nl().keyword("ELSE").space()
            printBranchCondition(caseStatement, caseStatement.elseCase)
            caseStatement.elseCase.accept(this)
        }

        sb.nl().decreaseIndent().appendIdent().keyword("END_CASE").printf(";")
    }

    override fun visit(ifStatement: IfStatement) {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            sb.nl()

            if (i == 0) {
                sb.keyword("IF").space()
            } else {
                sb.keyword("ELSIF").space()
            }

            ifStatement.conditionalBranches[i].condition.accept(this)

            sb.space().keyword("THEN").increaseIndent()

            printBranchCondition(ifStatement, ifStatement.conditionalBranches[i])

            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.decreaseIndent()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.nl().keyword("ELSE").increaseIndent()
            printBranchCondition(ifStatement, ifStatement.elseBranch)
            ifStatement.elseBranch.accept(this)
            sb.decreaseIndent()
        }
        sb.nl().keyword("END_IF")
    }
}