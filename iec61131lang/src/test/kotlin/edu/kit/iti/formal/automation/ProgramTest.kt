package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.PouElements
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File
import java.io.IOException
import java.util.*


@RunWith(Parameterized::class)
class ProgramTest(var testFile: File) {
    @Test
    @Throws(IOException::class)
    fun testParser() {
        val lexer = IEC61131Lexer(CharStreams.fromPath(testFile!!.toPath()))

        /*
        Vocabulary v = lexer.getVocabulary();
        for (Token t : lexer.getAllTokens()) {
            System.out.format("%20s : %10s @%d:%d%n",
                    t.getText(), v.getDisplayName(t.getType()), t.getLine(),
                    t.getCharPositionInLine());
        }
*/

        val parser = IEC61131Parser(CommonTokenStream(lexer))
        parser.addErrorListener(NiceErrorListener(testFile!!.name))
        val ctx = parser.start()
        Assert.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
        val sl = ctx.accept(IECParseTreeToAST()) as PouElements
        Assert.assertEquals(sl, sl.clone())
    }

    /*
    @Test
    public void testParseTreetoAST() throws IOException {
        PouElements tle = IEC61131Facade.file(new ANTLRFileStream(testFile));
        // Compare generated and original code
        Assert.assertEquals(IEC61131Facade.print(tle),
                Files.readAllLines(Paths.get(testFile)).stream().collect(Collectors.joining("\n")));
    }
    */


    @Test
    @Throws(IOException::class)
    fun testResolveDataTypes() {
        val tle = IEC61131Facade.file(testFile!!)
        val gs = IEC61131Facade.resolveDataTypes(tle)
        /*for (ClassDeclaration classDeclaration : gs.getClasses().values()) {
            Assert.assertTrue(
                    classDeclaration.getParent().getIdentifier() == null
                    || classDeclaration.getParentClass() != null);
            classDeclaration.getInterfaces().forEach(
                    i -> Assert.assertNotNull("Could not resolve interface for classes.",
                            i.getObj()));
        }
        for (FunctionBlockDeclaration functionBlockDeclaration : gs.getFunctionBlocks().values()) {
            Assert.assertTrue(functionBlockDeclaration.getParent().getIdentifier() == null
                    || functionBlockDeclaration.getParentClass() != null);
            functionBlockDeclaration.getInterfaces()
                    .forEach(i -> Assert.assertNotNull("Could not resolve interface for function blocks.",
                            i.getObj()));
        }*/
    }

    // @Test
    @Throws(IOException::class)
    fun testPrintTopLevelElements() {
        val tle = IEC61131Facade.file(testFile!!)
        PrettyPrinterTest.testPrettyPrintByString(tle, testFile)
    }

    @Test
    @Throws(IOException::class)
    fun testPrintTopLevelElementsByEquals() {
        val tle = IEC61131Facade.file(testFile!!)
        PrettyPrinterTest.testPrettyPrintByEquals(tle)
    }

    companion object {
        internal fun getResources(folder: String): Array<File>? {
            val f = ProgramTest::class.java.classLoader.getResource(folder)
            if (f == null) {
                System.err.format("Could not find %s%n", folder)
                return arrayOf()
            }
            val file = File(f.file)
            return file.listFiles()
        }

        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun get(): Iterable<Array<Any>> {
            val resources = getResources("edu/kit/iti/formal/automation/st/programs")
            val list = ArrayList<Array<Any>>()
            for (f in resources!!) {
                list.add(arrayOf(f))
            }
            return list
        }
    }

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
