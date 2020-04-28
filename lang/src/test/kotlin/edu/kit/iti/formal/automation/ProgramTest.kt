package edu.kit.iti.formal.automation

import LoadHelp
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.PouElements
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.nio.file.Path

object ProgramTest {
    @ParameterizedTest
    @MethodSource("getPrograms")
    fun testParser(testFile: Path) {
        val lexer = IEC61131Lexer(CharStreams.fromPath(testFile))
        /*
        Vocabulary v = lexer.getVocabulary();
        for (Token t : lexer.getAllTokens()) {
            System.out.format("%20s : %10s @%d:%d%n",
                    t.getText(), v.getDisplayName(t.getType()), t.getLine(),
                    t.getCharPositionInLine());
        }
*/
        val parser = IEC61131Parser(CommonTokenStream(lexer))
        parser.addErrorListener(NiceErrorListener(testFile.toString()))
        val ctx = parser.start()
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
        val sl = ctx.accept(IECParseTreeToAST()) as PouElements
        Assertions.assertEquals(sl, sl.setAllMetadata())
    }

    /*
    @Test
    public void testParseTreetoAST() throws IOException {
        PouElements tle = IEC61131Facade.file(new ANTLRFileStream(testFile));
        // Compare generated and original code
        Assertions.assertEquals(IEC61131Facade.printf(tle),
                Files.readAllLines(Paths.get(testFile)).stream().collect(Collectors.joining("\n")));
    }
    */


    @ParameterizedTest
    @MethodSource("getPrograms")
    fun testResolveDataTypes(testFile: Path) {
        val tle = IEC61131Facade.file(testFile)
        val gs = IEC61131Facade.resolveDataTypes(tle)
        /*for (ClassDeclaration classDeclaration : gs.getClasses().values()) {
            Assertions.assertTrue(
                    classDeclaration.getParent().getIdentifier() == null
                    || classDeclaration.getParentClass() != null);
            classDeclaration.getInterfaces().forEach(
                    i -> Assertions.assertNotNull("Could not resolve interface for classes.",
                            i.getObj()));
        }
        for (FunctionBlockDeclaration functionBlockDeclaration : gs.getFunctionBlocks().values()) {
            Assertions.assertTrue(functionBlockDeclaration.getParent().getIdentifier() == null
                    || functionBlockDeclaration.getParentClass() != null);
            functionBlockDeclaration.getInterfaces()
                    .forEach(i -> Assertions.assertNotNull("Could not resolve interface for function blocks.",
                            i.getObj()));
        }*/
    }

    @ParameterizedTest
    @MethodSource("getPrograms")
    @Disabled
    fun testPrintTopLevelElements(testFile: Path) {
        val tle = IEC61131Facade.file(testFile)
        PrettyPrinterTest.testPrettyPrintByString(tle, testFile)
    }

    @ParameterizedTest
    @MethodSource("getPrograms")
    fun testPrintTopLevelElementsByEquals(testFile: Path) {
        val tle = IEC61131Facade.file(testFile)
        PrettyPrinterTest.testPrettyPrintByEquals(tle)
    }

    @JvmStatic
    fun getPrograms() = LoadHelp.getPrograms()

    /*
    @Test
    public void testEffectiveSubtypes() throws IOException {
        PouElements tle = IEC61131Facade.INSTANCE.file(testFile);
        Scope gs = IEC61131Facade.INSTANCE.resolveDataTypes(tle);
        EffectiveSubtypeScope subtypeScope = OOIEC61131Facade.INSTANCE.findEffectiveSubtypes(tle, gs, new InstanceScope(gs));
        AstVisitor<Object> effectiveSubtypesPrinter = new AstVisitor<Object>() {
            @Override
            public Object visit(VariableDeclaration variableDeclaration) {
                if (FindEffectiveSubtypes.Companion.containsInstance(variableDeclaration)
                    && !subtypeScope.getTypes(variableDeclaration).isEmpty()) {
                    System.out.println(variableDeclaration);
                    for (AnyDt dataType : subtypeScope.getTypes(variableDeclaration))
                        System.out.println("* " + dataType.getName());
                    System.out.println();
                }
                return super.visit(variableDeclaration);
            }
        };
        tle.accept(effectiveSubtypesPrinter);
    }*/
}
