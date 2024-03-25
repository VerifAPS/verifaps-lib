package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.*
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.specification.smtlib.SExpression.Companion.fromText
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import org.junit.Assert
import org.junit.jupiter.api.Test
import org.junit.experimental.categories.Category
import java.io.IOException
import java.util.*
import java.util.function.Supplier

/**
 * Created by csicar on 09.02.17.
 */
class SmtEncoderTest {
    @Test //! Should take about 19min!
    @Category(Performance::class)
    fun performanceTest() {
        val sourceFileGetter = Supplier { SmtEncoderTest::class.java.getResourceAsStream("spec_long_example.xml") }
        val validSpec = TestUtils.importValidSpec(sourceFileGetter.get())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFileGetter.get())
        val smtEncoder = SmtEncoder(3000, validSpec, freeVariables)
        val model = smtEncoder.constraint
        val constrains: List<SExpression?>? = model!!.globalConstraints
        println(model.toString())
    }

    @Test //! Takes about 3min!
    @Category(Performance::class)
    fun performanceSingleVariableTest() {
        val sourceFileGetter =
            Supplier { SmtEncoderTest::class.java.getResourceAsStream("spec_long_single_variable_example.xml") }
        val validSpec = TestUtils.importValidSpec(sourceFileGetter.get())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFileGetter.get())

        val smtEncoder = SmtEncoder(3000, validSpec, freeVariables)
        val model = smtEncoder.constraint

        val constrains: Collection<SExpression?>? = model!!.globalConstraints
        val header: Collection<SExpression?>? = model.variableDefinitions
        println(model.toString())
        println(model.toText()!!.length)
        println(header)
    }

    @Test
    fun testNoDuplicateDefinition() {
        val sourceFile = Supplier {
            XmlSessionImporterTest::class.java.getResourceAsStream(
                "spec_constraint_valid_enum_1.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum("colors", mutableListOf("red", "green", "blue"))
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val definitions: Collection<SExpression?> = output!!.distinctVariableDefinitions
        val nonDuplicate: Set<SExpression?> = LinkedHashSet(definitions)
        Assert.assertEquals(nonDuplicate, definitions)
    }

    @Test
    fun testEnums1() {
        val sourceFile = Supplier {
            XmlSessionImporterTest::class.java.getResourceAsStream(
                "spec_constraint_valid_enum_1.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints: List<SExpression?>? = output!!.globalConstraints

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
        val sourceFile = Supplier {
            XmlSessionImporterTest::class.java.getResourceAsStream(
                "spec_constraint_valid_enum_1.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints: List<SExpression?>? = output!!.globalConstraints

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
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "spec_all.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints: List<SExpression?>? = output!!.globalConstraints

        println(output.toString())


        testWithStatements(
            constraints,
            "( implies ( bvuge n_1 #x0000 ) ( not ( = |C_1_0| #x0032 ) ) )"
        )
    }

    @Test
    @Throws(Exception::class)
    fun testGetMaxDurations() {
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "spec_all.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val args = arrayOfNulls<Class<*>?>(1)
        args[0] = Int::class.javaPrimitiveType
        val getMaxDurations = smtEncoder.javaClass.getDeclaredMethod("getMaxDuration", *args)
        getMaxDurations.isAccessible = true
        Assert.assertEquals(0, getMaxDurations.invoke(smtEncoder, -1))
        Assert.assertEquals(0, getMaxDurations.invoke(smtEncoder, -100))
        Assert.assertEquals(3, getMaxDurations.invoke(smtEncoder, 0))
        Assert.assertEquals(1, getMaxDurations.invoke(smtEncoder, 1))
    }

    @Test
    fun testUnsupportedOperation() {
    }

    @Test(expected = IllegalStateException::class)
    fun testMismatchingUsedVariablesAndVariableDefinitions() {
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "spec_freevariable.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(
            sourceFile.get(),
            TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )

        val maxDuration = 5


        val smtEncoder = SmtEncoder(maxDuration, spec, emptyList())
        val output = smtEncoder.constraint
        val constraints: List<SExpression?>? = output!!.globalConstraints
        val definitions: Collection<SExpression?>? = output.variableDefinitions
    }

    @Test(expected = IllegalArgumentException::class)
    fun testDifferentLengthInputs() {
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "spec_all.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue", "orange", "black")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val smtEncoder = SmtEncoder(listOf(3), spec, freeVariables)
    }

    @Test
    fun testMjSmallerDuration() {
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "spec_constant.xml"
            )
        }

        val spec = TestUtils.importValidSpec(sourceFile.get())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDuration = 3

        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints: List<SExpression?>? = output!!.globalConstraints


        testWithStatements(
            constraints,
            "( bvuge n_0 #x0005 )",
            " ( bvule n_0 #x0003 )  ",
            "( implies  ( bvuge n_0 #x0000 )   ( = |C_0_0| #x002A )  )",
            " ( implies  ( bvuge n_0 #x0001 )   ( = |C_0_1| #x002A )  )",
            "( implies  ( bvuge n_0 #x0002 )   ( = |C_0_2| #x002A )  )"
        )
    }

    @Test
    fun testFreeVariablesDefaultValue() {
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "spec_freevariable.xml"
            )
        }

        val spec = TestUtils.importValidSpec(
            sourceFile.get(), TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )
        val freeVariables = TestUtils.importValidFreeVariables(
            sourceFile.get(),
            TypeEnum(
                "Color",
                mutableListOf("red", "green", "blue")
            )
        )

        val maxDuration = 50


        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints: List<SExpression?>? = output!!.globalConstraints
        val definitions: Collection<SExpression?>? = output.variableDefinitions

        println(output.toString())

        testWithStatements(definitions, "(assert (= |p| #x000F))")
        testWithStatements(definitions, "(assert (= |q| #x0001))")
        testWithStatements(definitions, "(assert (= |r| true))")
    }

    @Test
    fun testFreeVariablesDefaultValueSimple() {
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "spec_freevars.xml"
            )
        }

        val spec = TestUtils.importValidSpec(sourceFile.get())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDuration = 50


        val smtEncoder = SmtEncoder(maxDuration, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints: List<SExpression?>? = output!!.globalConstraints
        val definitions: Collection<SExpression?>? = output.variableDefinitions

        println(output.toString())
        println(output.toText())

        testWithStatements(definitions, "(assert (= |freevar| #x0000))")
    }

    @Test
    @Throws(ImportException::class)
    fun testImported() {
        val sourceFile = Supplier { SmtEncoderTest::class.java.getResourceAsStream("testSpec.xml") }

        val spec = TestUtils.importValidSpec(sourceFile.get())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDurations: List<Int> = listOf(7, 1, 2)

        val preprocessor = SmtEncoder(maxDurations, spec, freeVariables)
        println(preprocessor.constraint)
    }


    @Test
    @Throws(ImportException::class, IOException::class)
    fun testSimpleExample() {
        val sourceFile = Supplier {
            SmtEncoderTest::class.java.getResourceAsStream(
                "simpleBackwardsReferenceTestSpec.xml"
            )
        }

        val spec = TestUtils.importValidSpec(sourceFile.get())
        val freeVariables = TestUtils.importValidFreeVariables(sourceFile.get())

        val maxDurations: List<Int> = listOf(3, 5, 5)

        val smtEncoder = SmtEncoder(maxDurations, spec, freeVariables)
        val output = smtEncoder.constraint
        val constraints: Collection<SExpression?>? = output!!.globalConstraints

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

    private fun testWithStatements(constraints: Collection<SExpression?>?, vararg s: String) {
        val statements = s.map { fromText(it) }
        val missingStatements = statements.filter { !constraints!!.contains(it) }
        Assert.assertEquals("no statements should be missing", ArrayList<SExpression>(), missingStatements)
    }
}