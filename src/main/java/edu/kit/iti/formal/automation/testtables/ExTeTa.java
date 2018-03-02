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
package edu.kit.iti.formal.automation.testtables;


import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException;
import edu.kit.iti.formal.automation.exceptions.FunctionUndefinedException;
import edu.kit.iti.formal.automation.exceptions.UnknownVariableException;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;
import edu.kit.iti.formal.automation.testtables.builder.TableTransformation;
import edu.kit.iti.formal.automation.testtables.exception.GetetaException;
import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.options.Mode;
import edu.kit.iti.formal.automation.testtables.monitor.MonitorGeneration;
import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SMVType;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.ParseException;

import javax.xml.bind.JAXBException;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class ExTeTa {
    public static boolean DEBUG = true;

    public static void main(String[] args) {
        try {
            CommandLine cli = parse(args);
            run(cli);
        } catch (FunctionUndefinedException e) {
            e.printStackTrace();
            Report.fatal("Could not call %s",
                    e.getInvocation().getCalleeName());
        } catch (UnknownVariableException | ParseException e) {
            Report.fatal(e.getMessage());
        } catch (DataTypeNotDefinedException e) {
            Report.fatal("Could not parse the given ST sources. There is an unknown datatype. %s",
                    e.getMessage());
            e.printStackTrace();
        } catch (JAXBException e) {
            Report.fatal("%s: %s", e.getClass().getSimpleName(),
                    e.getMessage());
        } catch (IOException e) {
            Report.fatal("IOExcepton: %s", e.getMessage());
        } catch (GetetaException e) {
            Report.fatal("%s: %s", e.getClass().getSimpleName(),
                    e.getMessage());
        } catch (Exception e) {
            e.printStackTrace();
            if (e.getMessage() == null) {
                Report.fatal(e.getClass().getName());
            } else {
                Report.fatal("%s: %s", e.getClass().getSimpleName(), e.getMessage());
            }
        }
    }

    public static void run(CommandLine cli) throws Exception {
        // xml
        Report.XML_MODE = cli.hasOption("x");

        //
        Runtime.getRuntime().addShutdownHook(new Thread(Report::close));

        //
        String tableFilename = cli.getOptionValue("t");
        String codeFilename = cli.getOptionValue("c");

        if (tableFilename == null || codeFilename == null) {
            Report.fatal("No code or table file given.");
            System.exit(1);
        }

        //
        GeneralizedTestTable table = Facade.readTable(tableFilename);
        OmegaSimplifier os = new OmegaSimplifier(table);
        os.run();
        if (!os.getIgnored().isEmpty()) {
            table = os.getProduct();
            System.out.printf("I ignore following rows: %s, because they are behind an \\omega duration.%n",
                    os.getIgnored());
        }


        //
        TopLevelElements code = Facade.readProgram(codeFilename);

        if (cli.getOptionValue('m') != null)
            switch (cli.getOptionValue('m')) {
                case "concrete-smv":
                    table.getOptions().setMode(Mode.CONCRETE_TABLE);
                    break;
                case "conformance":
                    table.getOptions().setMode(Mode.CONFORMANCE);
                    break;
                case "input-seq-exists":
                    table.getOptions().setMode(Mode.INPUT_SEQUENCE_EXISTS);
                    break;
                case "monitor":
                    table.getOptions().setMode(Mode.MONITOR_GENERATION);
                    break;
            }

        if (table.getOptions().getMode() == Mode.MONITOR_GENERATION) {
            MonitorGeneration mg = new MonitorGeneration(table);
            TopLevelElements fbs = mg.call();
            StructuredTextPrinter stp = new StructuredTextPrinter();
            fbs.accept(stp);
            System.out.println(stp.getString());
        } else {
            SMVModule modCode = evaluate(cli.hasOption("no-simplify"), code);
            SMVType superEnumType = Facade.createSuperEnum(code);
            TableTransformation tt = new TableTransformation(table,
                    superEnumType);
            SMVModule modTable = tt.transform();
            SMVModule mainModule = Facade
                    .glue(modTable, modCode, table.getOptions());

            List<SMVModule> modules = new LinkedList<>();
            modules.add(mainModule);
            modules.add(modTable);
            modules.add(modCode);
            modules.addAll(tt.getHelperModules());
            boolean b = Facade.runNuXMV(tableFilename, modules,
                    table.getOptions().getVerificationTechnique());

            if (Report.getMessage().getCounterexample() != null) {
                /*CounterExampleAnalyzer cea = new CounterExampleAnalyzer(table,
                        Report.getMessage());
                cea.run();*/
            }
        }
    }

    private static SMVModule evaluate(boolean disableSimplify, TopLevelElements code) {
        if (!disableSimplify)
            return SymbExFacade.evaluateProgram(code);
        else {
            ProgramDeclaration program = Utils.findProgram(code);
            return SymbExFacade.evaluateProgram(program, (TypeDeclarations) code.get(0),
                    program.getScope());
        }
    }

    private static CommandLine parse(String[] args) throws ParseException {
        CommandLineParser clp = new DefaultParser();

        org.apache.commons.cli.Options options = new org.apache.commons.cli.Options();
        options.addOption("x", false, "enable XML mode");
        options.addOption("", "no-simplify", false, "disable");
        options.addOption("t", "table", true, "the xml file of the table");
        options.addOption("o", "output", true, "ouput");
        options.addOption("c", "code", true, "program files");
        options.addOption("m", "mode", true, "mode");
        options.addOption("v", "technique", true, "verification technique");

        return clp.parse(options, args, true);
    }

}
