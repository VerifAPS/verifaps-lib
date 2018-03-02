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


import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.exceptions.FunctionUndefinedException
import edu.kit.iti.formal.automation.exceptions.UnknownVariableException
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.automation.st.ast.TopLevelElements
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations
import edu.kit.iti.formal.automation.testtables.builder.TableTransformation
import edu.kit.iti.formal.automation.testtables.exception.GetetaException
import edu.kit.iti.formal.automation.testtables.io.Report
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import edu.kit.iti.formal.automation.testtables.monitor.MonitorGeneration
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SMVType
import org.apache.commons.cli.CommandLine
import org.apache.commons.cli.CommandLineParser
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.ParseException

import javax.xml.bind.JAXBException
import java.io.IOException
import java.util.LinkedList

object ExTeTa {
    var DEBUG = true

    @JvmStatic
    fun main(args: Array<String>) {
        try {
            val cli = parse(args)
            run(cli)
        } catch (e: FunctionUndefinedException) {
            e.printStackTrace()
            Report.fatal("Could not call %s",
                    e.invocation.calleeName)
        } catch (e: UnknownVariableException) {
            Report.fatal(e.message)
        } catch (e: ParseException) {
            Report.fatal(e.message)
        } catch (e: DataTypeNotDefinedException) {
            Report.fatal("Could not parse the given ST sources. There is an unknown datatype. %s",
                    e.message)
            e.printStackTrace()
        } catch (e: JAXBException) {
            Report.fatal("%s: %s", e.javaClass.simpleName,
                    e.message)
        } catch (e: IOException) {
            Report.fatal("IOExcepton: %s", e.message)
        } catch (e: GetetaException) {
            Report.fatal("%s: %s", e.javaClass.simpleName,
                    e.message)
        } catch (e: Exception) {
            e.printStackTrace()
            if (e.message == null) {
                Report.fatal(e.javaClass.name)
            } else {
                Report.fatal("%s: %s", e.javaClass.simpleName, e.message)
            }
        }

    }

    @Throws(Exception::class)
    fun run(cli: CommandLine) {
        // xml
        Report.XML_MODE = cli.hasOption("x")

        //
        Runtime.getRuntime().addShutdownHook(Thread(Runnable { Report.close() }))

        //
        val tableFilename = cli.getOptionValue("t")
        val codeFilename = cli.getOptionValue("c")

        if (tableFilename == null || codeFilename == null) {
            Report.fatal("No code or table file given.")
            System.exit(1)
        }

        //
        var table: GeneralizedTestTable? = Facade.readTable(tableFilename)
        val os = OmegaSimplifier(table)
        os.run()
        if (!os.ignored.isEmpty()) {
            table = os.product
            System.out.printf("I ignore following rows: %s, because they are behind an \\omega duration.%n",
                    os.ignored)
        }


        //
        val code = Facade.readProgram(codeFilename)

        if (cli.getOptionValue('m') != null)
            when (cli.getOptionValue('m')) {
                "concrete-smv" -> table!!.options.mode = Mode.CONCRETE_TABLE
                "conformance" -> table!!.options.mode = Mode.CONFORMANCE
                "input-seq-exists" -> table!!.options.mode = Mode.INPUT_SEQUENCE_EXISTS
                "monitor" -> table!!.options.mode = Mode.MONITOR_GENERATION
            }

        if (table!!.options.mode == Mode.MONITOR_GENERATION) {
            val mg = MonitorGeneration(table)
            val fbs = mg.call()
            val stp = StructuredTextPrinter()
            fbs.accept<Any>(stp)
            println(stp.string)
        } else {
            val modCode = evaluate(cli.hasOption("no-simplify"), code)
            val superEnumType = Facade.createSuperEnum(code)
            val tt = TableTransformation(table,
                    superEnumType)
            val modTable = tt.transform()
            val mainModule = Facade
                    .glue(modTable, modCode, table.options)

            val modules = LinkedList<SMVModule>()
            modules.add(mainModule)
            modules.add(modTable)
            modules.add(modCode)
            modules.addAll(tt.helperModules)
            val b = Facade.runNuXMV(tableFilename, modules,
                    table.options.verificationTechnique)

            if (Report.message.getCounterexample() != null) {
                /*CounterExampleAnalyzer cea = new CounterExampleAnalyzer(table,
                        Report.getMessage());
                cea.run();*/
            }
        }
    }

    private fun evaluate(disableSimplify: Boolean, code: TopLevelElements): SMVModule {
        if (!disableSimplify)
            return SymbExFacade.evaluateProgram(code)
        else {
            val program = Utils.findProgram(code)
            return SymbExFacade.evaluateProgram(program, code[0] as TypeDeclarations,
                    program.scope)
        }
    }

    @Throws(ParseException::class)
    private fun parse(args: Array<String>): CommandLine {
        val clp = DefaultParser()

        val options = org.apache.commons.cli.Options()
        options.addOption("x", false, "enable XML mode")
        options.addOption("", "no-simplify", false, "disable")
        options.addOption("t", "table", true, "the xml file of the table")
        options.addOption("o", "output", true, "ouput")
        options.addOption("c", "code", true, "program files")
        options.addOption("m", "mode", true, "mode")
        options.addOption("v", "technique", true, "verification technique")

        return clp.parse(options, args, true)
    }

}
