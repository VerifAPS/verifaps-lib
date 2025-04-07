package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.stvs.*
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import java.io.IOException
import java.util.*
import kotlin.test.assertFailsWith

/**
 * Created by csicar on 09.02.17.
 */
class SmtEncoderTest {
    @Test //! Should take about 19min!
    @Tag("performance")
    fun performanceTest() {
        val sourceFileGetter = loaderFor("spec_long_example.xml")
        val validSpec = TestUtils.importValidSpec(sourceFileGetter())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFileGetter())
        val smtEncoder = SmtEncoder(3000, validSpec, freeVariables)
        val model = smtEncoder.constraint
        println(model.toString())
    }

    @Test //! Takes about 3min!
    @Tag("performance")
    fun performanceSingleVariableTest() {
        val sourceFileGetter =
            loaderFor("spec_long_single_variable_example.xml")
        val validSpec = TestUtils.importValidSpec(sourceFileGetter())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFileGetter())

        val smtEncoder = SmtEncoder(3000, validSpec, freeVariables)
        val model = smtEncoder.constraint

        val header = model.variableDefinitions
        println(model.toString())
        println(model.toText().length)
        println(header)
    }

    @Test
    fun testNoDuplicateDefinition() {
        val sourceFile =
            { XmlSessionImporterTest::class.java.getResourceAsStream("spec_constraint_valid_enum_1.xml")!! }

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum("colors", mutableListOf("red", "green", "blue"))
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val definitions = output.distinctVariableDefinitions
        val nonDuplicate = LinkedHashSet(definitions)
        Assertions.assertEquals(nonDuplicate, definitions)
    }

    @Test
    fun testEnums1() {
        val sourceFile = {
            XmlSessionImporterTest::class.java.getResourceAsStream("spec_constraint_valid_enum_1.xml")!!
        }

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints = output.globalConstraints

        println(output.toString())

        testWithStatements(
            constraints,
            "( bvsge |lala_2_2| #x0000 )",
            "( bvslt |lala_2_2| #x0003 )",
            "( bvsge |lala_2_1| #x0000 )",
            "( bvslt |lala_2_1| #x0003 )",
            "( bvsge |lala_2_0| #x0000 )",
            "( bvslt |lala_2_0| #x0003 )",
            "( bvsge |lala_1_0| #x0000 )",
            "( bvslt |lala_1_0| #x0003 )",
            "( bvsge |lala_0_2| #x0000 )",
            "( bvslt |lala_0_2| #x0003 )",
            "( bvsge |lala_0_1| #x0000 )",
            "( bvslt |lala_0_1| #x0003 )",
            "( bvsge |lala_0_0| #x0000 )",
            "( bvslt |lala_0_0| #x0003 )"
        )
    }

    @Test
    fun testEnums2() {
        val sourceFile = {
            XmlSessionImporterTest::class.java.getResourceAsStream("spec_constraint_valid_enum_1.xml")!!
        }

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints = output.globalConstraints

        println(output.toString())

        testWithStatements(
            constraints,
            "( bvsge |lala_2_2| #x0000 )",
            "( bvslt |lala_2_2| #x0005 )",
            "( bvsge |lala_2_1| #x0000 )",
            "( bvslt |lala_2_1| #x0005 )",
            "( bvsge |lala_2_0| #x0000 )",
            "( bvslt |lala_2_0| #x0005 )",
            "( bvsge |lala_1_0| #x0000 )",
            "( bvslt |lala_1_0| #x0005 )",
            "( bvsge |lala_0_2| #x0000 )",
            "( bvslt |lala_0_2| #x0005 )",
            "( bvsge |lala_0_1| #x0000 )",
            "( bvslt |lala_0_1| #x0005 )",
            "( bvsge |lala_0_0| #x0000 )",
            "( bvslt |lala_0_0| #x0005 )"
        )
    }

    @Test
    fun testNotEquals() {
        val sourceFile = loaderFor("spec_all.xml")

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints = output.globalConstraints

        println(output.toString())


        testWithStatements(
            constraints,
            "( implies ( bvuge n_1 #x0000 ) ( not ( = |C_1_0| #x0032 ) ) )"
        )
    }

    @Test
    @Throws(Exception::class)
    fun testGetMaxDurations() {
        val sourceFile = loaderFor("spec_all.xml")

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val args = arrayOfNulls<Class<*>?>(1)
        args[0] = Int::class.javaPrimitiveType
        val getMaxDurations = smtEncoder.javaClass.getDeclaredMethod("getMaxDuration", *args)
        getMaxDurations.isAccessible = true
        Assertions.assertEquals(0, getMaxDurations.invoke(smtEncoder, -1))
        Assertions.assertEquals(0, getMaxDurations.invoke(smtEncoder, -100))
        Assertions.assertEquals(3, getMaxDurations.invoke(smtEncoder, 0))
        Assertions.assertEquals(1, getMaxDurations.invoke(smtEncoder, 1))
    }

    @Test
    fun testMismatchingUsedVariablesAndVariableDefinitions() {
        val sourceFile = loaderFor("spec_freevariable.xml")

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(
            sourceFile(),
            TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )

        val maxDuration = 5
        assertFailsWith<IllegalStateException> {
            SmtEncoder(maxDuration, spec, emptyList())
        }
    }

    @Test
    fun testDifferentLengthInputs() {
        val sourceFile = loaderFor("spec_all.xml")

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())
        assertFailsWith<IllegalArgumentException> {
            SmtEncoder(listOf(3), spec, freeVariables)
        }
    }

    @Test
    fun testMjSmallerDuration() {
        val sourceFile = loaderFor("spec_constant.xml")

        val spec = TestUtils.importValidSpec(sourceFile())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints = output.globalConstraints


        testWithStatements(
            constraints,
            "( bvuge n_0 #x0005 )",
            " ( bvule n_0 #x0003 )  ",
            "( implies  ( bvuge n_0 #x0000 )   ( = |C_0_0| #x002A )  )",
            " ( implies  ( bvuge n_0 #x0001 )   ( = |C_0_1| #x002A )  )",
            "( implies  ( bvuge n_0 #x0002 )   ( = |C_0_2| #x002A )  )"
        )
    }

    private fun loaderFor(s: String) = { SmtEncoderTest::class.java.getResourceAsStream(s)!! }

    @Test
    fun testFreeVariablesDefaultValue() {
        val sourceFile = loaderFor("spec_freevariable.xml")

        val spec = TestUtils.importValidSpec(
            sourceFile(), TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(
            sourceFile(),
            TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )

        val maxDuration = 50


        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        output.globalConstraints
        val definitions = output.variableDefinitions

        println(output.toString())

        testWithStatements(definitions, "(assert (= |p| #x000F))")
        testWithStatements(definitions, "(assert (= |q| #x0001))")
        testWithStatements(definitions, "(assert (= |r| true))")
    }

    @Test
    fun testFreeVariablesDefaultValueSimple() {
        val sourceFile = loaderFor("spec_freevars.xml")

        val spec = TestUtils.importValidSpec(sourceFile())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDuration = 50


        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val definitions = output.variableDefinitions

        println(output.toString())
        println(output.toText())

        testWithStatements(definitions, "(assert (= |freevar| #x0000))")
    }

    @Test
    @Throws(ImportException::class)
    fun testImported() {
        val sourceFile = loaderFor("testSpec.xml")

        val spec = TestUtils.importValidSpec(sourceFile())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDurations: List<Int> = listOf(7, 1, 2)

        val preprocessor = SmtEncoder(maxDurations, spec, freeVariables)
        println(preprocessor.constraint)
    }


    @Test
    @Throws(ImportException::class, IOException::class)
    fun testSimpleExample() {
        val sourceFile = loaderFor("simpleBackwardsReferenceTestSpec.xml")

        val spec = TestUtils.importValidSpec(sourceFile())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile())

        val maxDurations: List<Int> = listOf(3, 5, 5)

        val smtEncoder = SmtEncoder(maxDurations, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints = output.globalConstraints

        println(output)


        testWithStatements(
            constraints,
            "(implies (bvuge n_2  #x0004) (= |A_2_4| |A_2_0|))",

            "(implies (bvuge n_2  #x0003) (= |A_2_3| |A_2_-1|))",
            "(implies (= n_1  #x0001) (= |A_2_-1| |A_1_0|))",

            "(implies (bvuge n_2  #x0002) (= |A_2_2| |A_2_-2|))",
            "(implies (= n_1  #x0001) (= |A_2_-2| |A_1_-1|))",
            "(implies (= n_0  #x0003) (= |A_1_-1| |A_0_2|))",

            "(implies (bvuge n_2  #x0001) (= |A_2_1| |A_2_-3|))",
            "(implies (= n_1  #x0001) (= |A_2_-3| |A_1_-2|))",
            "(implies (= n_0  #x0003) (= |A_1_-2| |A_0_1|))",

            "(implies (bvuge n_2  #x0000) (= |A_2_0| |A_2_-4|))",
            "(implies (= n_1  #x0001) (= |A_2_-4| |A_1_-3|))",
            "(implies (= n_0  #x0003) (= |A_1_-3| |A_0_0|))"
        )

        testWithStatements(
            constraints,
            "(implies (bvuge n_2  #x0004) (= |A_2_4| |A_2_0|))",

            "(implies (bvuge n_2  #x0003) (= |A_2_3| |A_2_-1|))",
            "(implies (= n_1  #x0002) (= |A_2_-1| |A_1_1|))",

            "(implies (bvuge n_2  #x0002) (= |A_2_2| |A_2_-2|))",
            "(implies (= n_1  #x0002) (= |A_2_-2| |A_1_0|))",

            "(implies (bvuge n_2  #x0001) (= |A_2_1| |A_2_-3|))",
            "(implies (= n_1  #x0002) (= |A_2_-3| |A_1_-1|))",
            "(implies (= n_0  #x0003) (= |A_1_-1| |A_0_2|))",


            "(implies (bvuge n_2  #x0000) (= |A_2_0| |A_2_-4|))",
            "(implies (= n_1  #x0002) (= |A_2_-4| |A_1_-2|))",
            "(implies (= n_0  #x0003) (= |A_1_-2| |A_0_1|))"
        )

        testWithStatements(
            constraints,
            "(bvuge n_0  #x0003)",
            "(bvule n_0  #x0003)",

            "(bvuge n_1  #x0001)",
            "(bvule n_1  #x0005)",

            "(bvuge n_2  #x0001)",
            "(bvule n_2  #x0005)"
        )
    }

    private fun testWithStatements(constraints: Collection<SExpr>, vararg s: String) {
        val statements = s.map { fromText(it) }
        val missingStatements = statements.filter { !constraints.contains(it) }
        Assertions.assertEquals(ArrayList<SExpr>(), missingStatements, "no statements should be missing")
    }
}