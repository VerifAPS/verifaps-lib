package edu.kit.iti.formal.automation.apps;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import com.google.common.base.Strings;
import edu.kit.iti.formal.automation.Console;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextLexer;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCFactory;
import edu.kit.iti.formal.automation.st.plcopenxml.SFCModelBuilder;
import edu.kit.iti.formal.automation.st0.CalculateExponentialBlowOff;
import edu.kit.iti.formal.automation.st0.ST0Factory;
import edu.kit.iti.formal.automation.symbex.SymbexFactory;
import edu.kit.iti.formal.automation.st.visitors.UtilsOld;
import edu.kit.iti.formal.automation.st.visitors.Visitable;
import edu.kit.iti.formal.automation.st.antlr.StructuredTextParser;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.st.plcopenxml.NiceErrorListener;
import edu.kit.iti.formal.automation.st.plcopenxml.model.SFCGraph;
import edu.kit.iti.formal.automation.st.util.UsageFinder;
import edu.kit.iti.formal.automation.st.visitors.VFactory;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.apache.commons.io.FileUtils;

import javax.swing.*;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;


/**
 * @author weigla
 * @date 04.07.2014
 */
@Parameters(commandNames = "transform", commandDescription = "transforms multiple pclopenxml files into smv modules")
public class Transformer extends App {
    private static JCommander instance;

    @Parameter(names = "--inputs", description = "input files", required = true)
    List<String> inputFiles = new ArrayList<>();

    @Parameter(names = "-debug", description = "Debug mode")
    static boolean debug = false;

    @Parameter(names = "-st", description = "Start with st (no xml input)")
    public boolean startWithST = false;

    @Parameter(names = "--main", description = "output name of the smv module", required = true)
    String mainModule;


    public void execute() throws IOException {
        if (inputFiles.size() == 0) {
            showOpenFileDialog();
        }

        Set<ModuleDeclaration> modules = new HashSet<>();

        for (String input : inputFiles) {
            File fInput = new File(input);
            modules.add(processfile(fInput));
        }

        buildMainModule(modules);
    }

    private void buildMainModule(Set<ModuleDeclaration> modules) throws IOException {
        Set<VariableDeclaration> ivar = new TreeSet<>();
        Set<VariableDeclaration> output = new TreeSet<>();

        for (ModuleDeclaration module : modules) {
            Set<VariableDeclaration> iset = module.getScope().getVariableMap().values()
                    .stream()
                    .filter(ModuleDeclaration::isInputVariable)
                    .collect(Collectors.toSet());

            ivar.addAll(iset);

            Set<VariableDeclaration> oset = module.getScope().getVariableMap().values()
                    .stream()
                    .filter(ModuleDeclaration::isOutputVariable)
                    .collect(Collectors.toSet());

            output.addAll(oset);

        }


        CodeWriter cw = new CodeWriter();

        cw.append("MODULE main");
        cw.nl().append("IVAR").increaseIndent();

        for (VariableDeclaration vd : ivar) {
            cw.nl().append(vd.getName()).append(" : ");

           if (vd.getDataType() instanceof EnumerateType) {
                EnumerateType dataType = (EnumerateType) vd.getDataType();
                cw.append("{");

                cw.append(implode(", ", dataType.getAllowedValues()));

                for (String val : dataType.getAllowedValues()) {
                    cw.append(val).append(", ");
                }
                //sb.deleteLast(2);
                cw.append("}");
            } else {
                cw.append(ModuleDeclaration.smvDataTypeName(vd.getDataTypeName(), vd.getDataType()));
            }
            cw.append(ModuleDeclaration.varFlags(vd));
        }

        cw.decreaseIndent().nl().append("VAR").increaseIndent();

        for (ModuleDeclaration module : modules) {
            String s = module.getScope().getVariableMap().values()
                    .stream()
                    .filter(ModuleDeclaration::isInputVariable)
                    .map(VariableDeclaration::getName)
                    .reduce((a, b) -> (a + ",\n         " + b)).orElse("");

            cw.nl();
            cw.append(module.getModuleName().toLowerCase()).append(" : ").append(module.getModuleName())
                    .append("(").append(s).append(");");
        }


        cw.decreaseIndent().nl().append("DEFINE").increaseIndent();

        cw.nl().append("premise := TRUE;");


        String[] onames = new String[output.size()];
        int i = 0;

        for (VariableDeclaration vd : output) {
            String conjunction = "TRUE";
            String previous = null;

            for (ModuleDeclaration module : modules) {
                if (module.getScope().getVariableMap().containsKey(vd.getName())) {
                    String cur = module.getModuleName().toLowerCase() + "." + vd.getName();
                    if (previous != null) {
                        conjunction += " & " + previous + " = " + cur;
                    }
                    previous = cur;
                }
            }

            String name = vd.getName();
            onames[i++] = name;
            cw.nl().append(name).append(" := ").append(conjunction).append(";");
        }


        cw.decreaseIndent().nl().nl().append("LTLSPEC ").increaseIndent();
        cw.nl().append(" G (premise -> ").append(implode(" & ", onames)).append(");");


        cw.decreaseIndent();

        for (ModuleDeclaration module : modules) {
            cw.nl().nl();
            cw.append("-- ").append(Strings.repeat("-", 77));
            cw.nl();
            cw.append(module.toString());
            cw.nl();
        }

        FileUtils.writeStringToFile(new File(mainModule), cw.toString());

    }

    public static String implode(String s, String[] allowedValues) {
        return Arrays.asList(allowedValues).stream().reduce((a, b) -> (a + s + b)).orElse("");
    }

    public ModuleDeclaration processfile(File fInput) throws IOException {
        Console.info("Processing: %s", fInput);

        //assume xml pclopen:
        TopLevelElements ast;
        if (!startWithST) {
            ast = buildSFC(fInput);
        } else {
            ast = parse(fInput);
        }

        SFCFactory.injectPreamble(ast);

        TopLevelElements st0ast = ST0Factory.simplify(ast);

        /*String st00 = VFactory.ast2St(st0ast, false);
        File file = new File(fInput.getAbsolutePath() + "_.st00");
        FileUtils.writeStringToFile(file,st00);
        st0ast = parse(file);*/

        remarkProgramInputVariables(st0ast);

        //test
        System.out.println("BlowOff: " + CalculateExponentialBlowOff.calc(st0ast.get(1)));


        writeAST(new File(fInput.getAbsolutePath() + ".st0"),
                st0ast);

        String name = fInput.getName().replace("_Final.xml", "");


        //ModuleDeclaration md = SymbexFactory.toCaseExpression(st0ast);
        ModuleDeclaration md = SymbexFactory.toCaseExpressionMU(st0ast, name);

        try (FileWriter fw = new FileWriter(new File(fInput.getAbsolutePath() + ".smv"))) {
            md.toString(new CodeFileWriter(fw));
        } finally {
        }

        try (FileWriter fw = new FileWriter(new File(fInput.getAbsolutePath() + ".vardep.dot"))) {
            fw.write(md.dotVarGraph());
        } finally {
        }

        printExpBlowOff(st0ast);

        return md;
    }

    private void printExpBlowOff(TopLevelElements st0ast) {
        Console.debug("BlowOff: " + CalculateExponentialBlowOff.calc(st0ast.get(1)));
    }

    public static TopLevelElements buildSFC(File fInput) throws IOException {
        if (debug) {
            for (SFCGraph g : SFCFactory.sfcToGraph(fInput)) {
                FileUtils.writeStringToFile(
                        new File(fInput.getAbsolutePath() + "_" + g.getName() + ".dot"),
                        g.toDot());
            }
        }

        TopLevelElements ast = SFCFactory.sfcToSt(fInput);
        writeSeperatedAST(fInput, ast);
        writeAST(fInput, ast);
        return ast;
    }

    static void writeAST(File fInput, TopLevelElements ast) throws IOException {
        FileUtils.writeStringToFile(
                new File(fInput.getAbsolutePath() + ".st"),
                VFactory.ast2St(ast, debug));

        if (debug) {
            FileUtils.writeStringToFile(
                    new File(fInput.getAbsolutePath() + ".st.html"),
                    VFactory.ast2Html(ast, debug));
        }
    }

    private static void writeSeperatedAST(File fInput, TopLevelElements ast) throws IOException {
        for (TopLevelElement e : ast) {
            writeAST(new File(fInput.getAbsolutePath() + "_" + e.getBlockName()), e);
        }
    }

    private static void writeAST(File fInput, Visitable ast) throws IOException {
        FileUtils.writeStringToFile(
                new File(fInput.getAbsolutePath() + ".st"),
                VFactory.ast2St(ast, debug));

        if (debug) {
            FileUtils.writeStringToFile(
                    new File(fInput.getAbsolutePath() + ".st.html"),
                    VFactory.ast2Html(ast, debug));
        }
    }

    private void remarkProgramInputVariables(TopLevelElements st0ast) {
        ProgramDeclaration pd = UtilsOld.findProgram(st0ast);
        UsageFinder waf = UsageFinder.investigate(pd);
        //Set<String> wbrVariables = WriteBeforeReadIdentifier.investigate(pd);

        for (VariableDeclaration vd : pd.getScope()) {
            String var = vd.getName();

            //if (wbrVariables.contains(var)) {
            //    vd.setType(vd.getType() | VariableDeclaration.WRITE_BEFORE_READ);
            //}

            if (waf.getReadedReference().contains(var)) {
                vd.setType(vd.getType() | VariableDeclaration.READED);
            } else {
                vd.setType(vd.getType() | VariableDeclaration.NOT_READED);
            }

            if (waf.getWrittenReferences().contains(var)) {
                vd.setType(vd.getType() | VariableDeclaration.WRITTEN_TO);
            }


        }


    }

    public static TopLevelElements parse(File file) {

        try {
            CharStream afs = new ANTLRFileStream(file.getAbsolutePath());
            StructuredTextLexer lexer = new StructuredTextLexer(afs);
            StructuredTextParser p = new StructuredTextParser(new CommonTokenStream(lexer));
            //p.removeErrorListeners();

            p.addErrorListener(new NiceErrorListener(FileUtils.readFileToString(file)));

            return new TopLevelElements(p.start());

        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }

    private TopLevelElements parse(String st00) {
        return new TopLevelElements(SFCModelBuilder.getStructuredTextParser(st00).start());
    }

    private TopLevelElements writeAndRead(TopLevelElements st0ast) {
        String st0 = VFactory.ast2St(st0ast, true);
        return new TopLevelElements(SFCModelBuilder.getStructuredTextParser(st0).start());
    }

    private void showOpenFileDialog() {
        JFileChooser jfc = new JFileChooser(".");
        jfc.setMultiSelectionEnabled(true);
        int c = jfc.showOpenDialog(null);
        if (c == JFileChooser.APPROVE_OPTION) {
            for (File f : jfc.getSelectedFiles()) {
                inputFiles.add(f.getAbsolutePath());
            }
            Console.info(String.format("Selected %s", Arrays.toString(jfc.getSelectedFiles())));
        } else {
            Console.info("Abort by user.");
        }

    }

}
