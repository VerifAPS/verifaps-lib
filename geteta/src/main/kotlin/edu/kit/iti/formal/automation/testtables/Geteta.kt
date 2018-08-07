/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables


import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.testtables.io.Report
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.smv.ast.SMVModule

class GetetaApp : CliktCommand(
        epilog = "Geteta -- Tooling for Generalized Test Tables.",
        name = "geteta.sh") {
    val xmlModeOutput by option("x", help = "enable XML mode")
            .flag(default = false)

    val disableSimplify by option("--no-simplify", help = "disable")
            .flag(default = false)

    val table by option("-t", "--table", help = "the xml file of the table", metavar = "FILE")
            .required()

    val outputFolder by option("-o", "--output", help = "Output directory")

    val codeFiles by option("-c", "--code", help = "program files")

    val mode by option("-m", "--mode", help = "Verification Mode")

    val verificationTechnique by option("-v", "--technique",
            help = "verification technique")

    override fun run() {
        Runtime.getRuntime().addShutdownHook(Thread(Runnable { Report.close() }))

        if (codeFiles == null) {
            Report.fatal("No code or table file given.")
            System.exit(1)
        }

        /*TODO
        var table = GetetaFacade.parseTableXML(tableFilename)
        val os = OmegaSimplifier(table)
        os.run()
        if (!os.ignored.isEmpty()) {
            table = os.product
            System.out.printf("I ignore following rows: %s, because they are behind an \\omega duration.%n",
                    os.ignored)
        }


        //
        val code = GetetaFacade.readProgram(codeFilename)

        if (cli.getOptionValue('m') != null)
            when (cli.getOptionValue('m')) {
                "concrete-smv" -> table.options.mode = Mode.CONCRETE_TABLE
                "conformance" -> table.options.mode = Mode.CONFORMANCE
                "input-seq-exists" -> table.options.mode = Mode.INPUT_SEQUENCE_EXISTS
                "monitor" -> table.options.mode = Mode.MONITOR_GENERATION
            }

        if (table.options.mode == Mode.MONITOR_GENERATION) {
            val mg = MonitorGeneration(table)
            val fbs = mg.call()
            val stp = StructuredTextPrinter()
            fbs.accept(stp)
            println(stp.string)
        } else {
            val modCode = evaluate(cli.hasOption("no-simplify"), code)
            val superEnumType = GetetaFacade.createSuperEnum(code)
            val tt = TableTransformation(table,
                    superEnumType,
                    true)
            val modTable = tt.transform()
            val mainModule = GetetaFacade
                    .glue(modTable, modCode, table.options)

            val modules = LinkedList<SMVModule>()
            modules.add(mainModule)
            modules.add(modTable)
            modules.add(modCode)
            modules.addAll(tt.model.helperModules)
            val b = GetetaFacade.runNuXMV(tableFilename, modules,
                    table.options.verificationTechnique)

            if (Report.message.getCounterexample() != null) {
                /*CounterExampleAnalyzer cea = new CounterExampleAnalyzer(table,
                        Report.getMessages());
                cea.run();*/
            }
        }
        */
    }

    private fun evaluate(disableSimplify: Boolean, code: PouElements): SMVModule {
        return SymbExFacade.evaluateProgram(Utils.findProgram(code)!!, disableSimplify)
    }
}

class FunctionVerification : CliktCommand() {
    override fun run() {

    }
}