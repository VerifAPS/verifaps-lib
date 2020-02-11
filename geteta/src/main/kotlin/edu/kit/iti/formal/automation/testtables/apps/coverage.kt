package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.rvt.ExpressionReplacer
import edu.kit.iti.formal.automation.smt.*
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.smt.SList
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

class CoverageApp : CliktCommand(
        epilog = "ttcov -- Program Coverage with Test Tables.",
        name = "ttcov") {
    val disableSimplify by option("--no-simplify", help = "disable")
            .flag("--simplify", default = false)

    val table by option("-t", "--table", help = "the xml file of the table", metavar = "FILE")
            .file(exists = true, readable = true)
            .required()

    val outputFolder by option("-o", "--output", help = "Output directory")

    val library by option("-L", "--library", help = "library files").file().multiple()
    val program by option("-P", "--program", "-c", help = "program files").file(exists = true, readable = true).required()

    override fun run() {
        val gtts = readTable()
        val code = IEC61131Facade.readProgramsWLP(library, listOf(program)).first()
                ?: throw IllegalStateException("No program given in $program")
        val (lineMap, modCode) = SymbExFacade.evaluateProgramWithLineMap(code, disableSimplify)
        info("Program evaluation")

        val superEnumType = GetetaFacade.createSuperEnum(listOf(code.scope))
        info("Super enum built")

        val definitions = modCode.definitions.map { it.target.name to it.expr }.toMap()
        //val r = ExpressionReplacer(definitions)
        modCode.unfold()

        val dtTranslator: S2SDataTypeTranslator = DefaultS2STranslator()
        val fnTranslator: S2SFunctionTranslator = DefaultS2SFunctionTranslator()
        val toSmt = Smv2SmtVisitor(fnTranslator, dtTranslator, "")
        val toSmtState = Smv2SmtVisitor(fnTranslator, dtTranslator, "old")
        val program = SMTFacade.translate(modCode)


        gtts.forEach { gtt ->
            val varRename = hashMapOf<SMVExpr,SMVExpr>()
            gtt.programVariables.forEach {
                    val internalVariable = it.internalVariable(gtt.programRuns)
                varRename[internalVariable] =
                            SVariable(if(it.isAssumption) "old${it.name}" else "new${it.name}", internalVariable.dataType!!)
            }
            var renamer = ExpressionReplacer(varRename)

            File(outputFolder, "${gtt.name}.smt2").bufferedWriter().use { out ->
                out.write(";;Preamble\n${program.preamble}\n;;--\n")
                out.write(program.getStepDefinition(true, "old"))
                out.newLine()
                out.write(program.getStepDefinition(false, "new"))
                out.newLine()
                out.write(SList("assert", program.nextBody).toString())
                out.newLine()
                //println(program.getAssertNext("_cur", "_new"))
                gtt.region.flat().forEach {
                    val assume = it.inputExpr.values.conjunction(SLiteral.TRUE).accept(renamer).accept(toSmt)
                    val assert = it.outputExpr.values.conjunction(SLiteral.TRUE).accept(renamer).accept(toSmt)
                    out.write("""
                        (push)  ;; Table row ${it.id}
                        (assert $assume) ;; pre-condition
                        (assert $assert) ;; post-condition
                    """.trimIndent())
                    lineMap.branchMap.forEach { (t, _) ->
                        val e = definitions[t]?.accept(toSmtState)
                        out.write("\t(push) (assert ${e}) (check-sat) (pop);; check for $t")
                        out.newLine()
                    }
                    out.write("(pop)\n")
                }
            }
        }
    }

    private fun readTable() = table.let {
        info("Use table file ${it.absolutePath}")
        GetetaFacade.readTables(it)
    }.map {
        it.ensureProgramRuns()
        it.generateSmvExpression()
        it.simplify()
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
