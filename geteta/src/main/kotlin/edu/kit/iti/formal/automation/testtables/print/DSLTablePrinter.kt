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
package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.conjunction
import edu.kit.iti.formal.util.CodeWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.07.18)
 */
class DSLTablePrinter(val stream: CodeWriter) {
    lateinit var gtt: GeneralizedTestTable

    // lateinit var controlFields: List<String>
    fun print(gtt: GeneralizedTestTable) {
        this.gtt = gtt

        /*controlFields = gtt.programRuns.map { pauseVariableTT(it) } +
                gtt.chapterMarksForProgramRuns.flatMap { (run, rows) ->
                    rows.map { setVariableTT(it, gtt.programRuns[run]) }
                } +
                gtt.chapterMarksForProgramRuns.flatMap { (run, rows) ->
                    rows.map { resetVariableTT(it, gtt.programRuns[run]) }
                }*/

        stream.printf("table ${gtt.name} {")
        stream.increaseIndent()
        gtt.programVariables.forEach(this::print)
        stream.nl()
        gtt.constraintVariables.forEach(this::print)
        stream.nl()
        print(gtt.properties)
        stream.nl()
        print(gtt.region)
        stream.nl()
        gtt.functions.forEach(this::print)

        stream.decreaseIndent().nl().printf("}")
    }

    fun print(v: ColumnVariable) {
        if (v is ProgramVariable) print(v)
        if (v is ProjectionVariable) print(v)
    }

    fun print(v: ProjectionVariable) {
        if (v.category == ColumnCategory.ASSUME) {
            stream.print("assume ")
        } else {
            stream.print("assert ")
        }
    }

    fun print(v: ProgramVariable) {
        stream.nl().printf("column ")
        if (v.isState) {
            stream.print("state ")
            if (v.category == ColumnCategory.ASSUME) {
                stream.print("assume ")
            } else {
                stream.print("assert ")
            }
            if (v.isNext) {
                stream.print("next")
            }
        } else {
            if (v.category == ColumnCategory.ASSERT) {
                if (v.isNext) {
                    stream.print("output ")
                } else {
                    stream.print("assert ")
                }
            } else {
                if (v.isNext) {
                    stream.print("assume next")
                } else {
                    stream.print("input")
                }
            }
        }

        if (v.realName == v.name) {
            stream.printf(v.name).printf(" : ").print(v.dataType)
        } else {
            stream.printf(v.realName).printf(" : ").print(v.dataType).printf(" as ")
                .printf(v.name)
        }
    }

    fun print(v: ConstraintVariable) {
        stream.nl().printf("gvar ").printf(v.name).printf(" : ").print(v.dataType)
        if (v.constraint != null) {
            stream.printf(" with ").printf(v.constraint!!.text)
        }
    }

    fun print(p: MutableMap<String, String>) {
        if (p.isEmpty()) return
        stream.nl().printf("options {").increaseIndent()
        p.forEach { t, u ->
            stream.nl().printf("$t = $u")
        }
        stream.nl().decreaseIndent().printf("}")
    }

    fun print(r: TableNode) {
        stream.nl()
        when (r) {
            is Region -> {
                stream.printf("group ${r.id} ")
                print(r.duration)
                stream.printf(" {").increaseIndent()
                r.children.forEach { print(it) }
                stream.decreaseIndent().nl().printf("}")
            }
            is TableRow -> {
                stream.printf("row ${r.id} ")
                print(r.duration)
                stream.printf("{").increaseIndent()
                val play = (gtt.programRuns.indices) - r.pauseProgramRuns.toSet()
                stream.nl().printf("\\play: %s", play.joinToString(", "))
                if (r.pauseProgramRuns.isNotEmpty()) {
                    stream.nl().printf("\\pause: %s", r.pauseProgramRuns.joinToString(", "))
                }
                r.controlCommands.filterIsInstance<ControlCommand.Backward>()
                    .forEach {
                        stream.nl().printf("\\backward(%s): %s", it.jumpToRow, it.affectedProgramRun)
                    }

                /*controlFields.forEach { it ->
                    stream.nl().printf("// $it: ${r.inputExpr[it]?.repr()}")
                }*/

                gtt.programVariables.forEach {
                    val raw = r.rawFields[it]
                    val smvName = it.internalVariable(gtt.programRuns).name
                    val unfolded = r.inputExpr[smvName]?.repr() ?: r.outputExpr[smvName]?.repr() ?: ""
                    val name = when (it) {
                        is ProgramVariable -> "${gtt.programRuns[it.programRun]}::${it.name}"
                        else -> it.name
                    }
                    stream.nl().printf("$name: ${raw?.text} //$unfolded")
                }

                val input = r.inputExpr.values.conjunction(SLiteral.TRUE)
                val output = r.outputExpr.values.conjunction(SLiteral.TRUE)
                stream.nl().printf("// input: ${input.repr()}")
                stream.nl().printf("// output: ${output.repr()}")

                stream.decreaseIndent().nl().printf("}")
            }
        }
    }

    fun print(d: Duration) = stream.write(
        when (d) {
            is Duration.Omega -> "omega"
            is Duration.ClosedInterval -> "[${d.lower}, ${d.upper}]" + d.modifier.repr()
            is Duration.OpenInterval -> ">= ${d.lower}" + d.modifier.repr()
        },
    )

    fun print(fs: FunctionDeclaration) {
        val stp = StructuredTextPrinter()
        stp.sb = stream
        fs.accept(stp)
    }
}