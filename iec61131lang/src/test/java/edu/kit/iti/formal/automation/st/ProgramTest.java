package edu.kit.iti.formal.automation.st;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.NiceErrorListener;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;


@RunWith(Parameterized.class)
public class ProgramTest {
    @Parameter public File testFile;

    public static final File[] getResources(String folder) {
        URL f = ProgramTest.class.getClassLoader().getResource(folder);
        if (f == null) {
            System.err.format("Could not find %s%n", folder);
            return new File[0];
        }
        File file = new File(f.getFile());
        return file.listFiles();
    }

    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getStructuredTextFiles() throws IOException {
        File[] resources = getResources("edu/kit/iti/formal/automation/st/programs");
        ArrayList<Object[]> list = new ArrayList<>();
        for (File f : resources) {
            list.add(new Object[]{f});
        }
        return list;
    }

    @Test
    public void testParser() throws IOException {
        IEC61131Lexer lexer = new IEC61131Lexer(CharStreams.fromPath(testFile.toPath()));

/*
        Vocabulary v = lexer.getVocabulary();
        for (Token t : lexer.getAllTokens()) {
            System.out.format("%20s : %10s @%d:%d%n",
                    t.getText(), v.getDisplayName(t.getType()), t.getLine(),
                    t.getCharPositionInLine());
        }
*/

        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        parser.addErrorListener(new NiceErrorListener(testFile.getName()));
        IEC61131Parser.StartContext ctx = parser.start();
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
        TopLevelElements sl = (TopLevelElements) ctx.accept(new IECParseTreeToAST());
        Assert.assertEquals(sl, sl.copy());
    }

    /*
    @Test
    public void testParseTreetoAST() throws IOException {
        TopLevelElements tle = IEC61131Facade.file(new ANTLRFileStream(testFile));
        // Compare generated and original code
        Assert.assertEquals(IEC61131Facade.print(tle),
                Files.readAllLines(Paths.get(testFile)).stream().collect(Collectors.joining("\n")));
    }
    */

    @Test
    public void testResolveDataTypes() throws IOException {
        TopLevelElements tle = IEC61131Facade.file(testFile);
        GlobalScope gs = IEC61131Facade.resolveDataTypes(tle);
        for (ClassDeclaration classDeclaration : gs.getClasses()) {
            Assert.assertTrue(classDeclaration.getParent().getIdentifier() == null
                    || classDeclaration.getParentClass() != null);
            classDeclaration.getInterfaces().forEach(i -> Assert.assertTrue(i.getIdentifiedObject() != null));
        }
        for (FunctionBlockDeclaration functionBlockDeclaration : gs.getFunctionBlocks()) {
            Assert.assertTrue(functionBlockDeclaration.getParent().getIdentifier() == null
                    || functionBlockDeclaration.getParentClass() != null);
            functionBlockDeclaration.getInterfaces()
                    .forEach(i -> Assert.assertTrue(i.getIdentifiedObject() != null));
        }
    }

    @Test
    public void testPrintTopLevelElements() throws IOException {
        TopLevelElements tle = IEC61131Facade.file(testFile);
        System.out.println(IEC61131Facade.printTopLevelElements(tle));
    }

    @Test
    public void testEffectiveSubtypes() throws IOException {
        TopLevelElements tle = IEC61131Facade.file(testFile);
        GlobalScope gs = IEC61131Facade.resolveDataTypes(tle);
        IEC61131Facade.findEffectiveSubtypes(tle, gs);
        AstVisitor effectiveSubtypesPrinter = new AstVisitor() {
            @Override
            public Object visit(VariableDeclaration variableDeclaration) {
                if (!variableDeclaration.getEffectiveDataTypes().isEmpty()) {
                    System.out.println(variableDeclaration);
                    for (Any dataType : variableDeclaration.getEffectiveDataTypes())
                        System.out.println("* " + dataType.getName());
                    System.out.println();
                }
                return super.visit(variableDeclaration);
            }
        };
        tle.accept(effectiveSubtypesPrinter);
    }
}
