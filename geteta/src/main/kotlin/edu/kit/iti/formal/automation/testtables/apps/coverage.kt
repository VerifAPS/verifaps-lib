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
package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.groups.provideDelegate
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import edu.kit.iti.formal.automation.CommonArguments
import edu.kit.iti.formal.automation.ProgramOptions
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.smt.*
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smv.ExpressionReplacer
import edu.kit.iti.formal.smv.SMVAstVisitor
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.conjunction
import edu.kit.iti.formal.util.info
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (2/11/20)
 */
object Coverage {
    @JvmStatic
    fun main(args: Array<String>) {
        CoverageApp().main(args)
    }
}

class CoverageApp : CliktCommand(name = "ttcov") {
    override fun helpEpilog(context: Context) = "ttcov -- Program Coverage with Test Tables."

    val common by CommonArguments()

    val tableArguments by TableArguments()
    val runSmt by option().flag()
    val outputFile by option("-o", "--output", help = "Output directory")

    val programOptions by ProgramOptions()
    val library = programOptions.library
    val program = programOptions.program

    override fun run() {
        common()

        val gtts = tableArguments.readTables()
        val code = programOptions.readProgram()
        val (lineMap, modCode) = SymbExFacade.evaluateProgramWithLineMap(code, programOptions.disableSimplify)
        info("Program evaluation")

        val superEnumType = GetetaFacade.createSuperEnum(listOf(code.scope))
        info("Super enum built")

        val definitions = modCode.definitions.map { it.target.name to it.expr }.toMap()
        // val r = ExpressionReplacer(definitions)
        modCode.unfold()

        val dtTranslator: S2SDataTypeTranslator = DefaultS2STranslator()
        val fnTranslator: S2SFunctionTranslator = DefaultS2SFunctionTranslator()
        val toSmt = Smv2SmtVisitor(fnTranslator, dtTranslator, "")
        val toSmtState = Smv2SmtVisitor(fnTranslator, dtTranslator, "old")
        val program = SmvSmtFacade.translate(modCode)

        gtts.forEach { gtt ->
            val varRename = hashMapOf<SMVExpr, SMVExpr>()
            gtt.programVariables.forEach {
                val internalVariable = it.internalVariable(gtt.programRuns)
                varRename[internalVariable] =
                    SVariable(if (it.isAssumption) "old${it.name}" else "new${it.name}", internalVariable.dataType!!)
            }
            var renamer = ExpressionReplacer(varRename)

            File(outputFile, "${gtt.name}.smt2").bufferedWriter().use { out ->
                out.write(";;Preamble\n${program.preamble}\n;;--\n")
                out.write(program.getStepDefinition(true, "old"))
                out.newLine()
                out.write(program.getStepDefinition(false, "new"))
                out.newLine()
                out.write(SList("assert", program.nextBody).toString())
                out.newLine()
                // println(program.getAssertNext("_cur", "_new"))
                gtt.region.flat().forEach {
                    val assume = it.inputExpr.values.conjunction(SLiteral.TRUE).accept(renamer).accept(toSmt)
                    val assert = it.outputExpr.values.conjunction(SLiteral.TRUE).accept(renamer).accept(toSmt)
                    out.write(
                        """
                        (push)  ;; Table row ${it.id}
                        (assert $assume) ;; pre-condition
                        (assert $assert) ;; post-condition
                        """.trimIndent(),
                    )
                    lineMap.branchMap.forEach { (t, _) ->
                        val e = definitions[t]?.accept(toSmtState)
                        out.write("\t(push) (assert $e) (check-sat) (pop);; check for $t")
                        out.newLine()
                    }
                    out.write("(pop)\n")
                }
            }
        }
    }
}

private fun SMVModule.unfold() {
    val defs = definitions.map { it.target to it.expr }.toMap()
    var m = defs.toMap()
    val r = ExpressionReplacer(defs)
    while (true) {
        r.changed = false
        val updated = m.map { (t, u) ->
            t to u.accept(r as SMVAstVisitor<SMVAst>) as SMVExpr
        }.toMap()
        m = updated
        if (!r.changed) break
    }

    definitions.clear()

    initAssignments.forEach { it.expr = it.expr.accept(r) as SMVExpr }
    nextAssignments.forEach { it.expr = it.expr.accept(r) as SMVExpr }
    transExpr = transExpr.map { it.accept(r) as SMVExpr }.toMutableList()
    initExpr = initExpr.map { it.accept(r) as SMVExpr }.toMutableList()
}