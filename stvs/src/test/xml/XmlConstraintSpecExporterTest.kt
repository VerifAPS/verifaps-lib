package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.expressions.Type
import org.apache.commons.io.IOUtils
import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.util.*

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecExporterTest {
    private var exporter: XmlConstraintSpecExporter? = null

    @Before
    fun setUp() {
        exporter = XmlConstraintSpecExporter()
    }

    @Test
    @Throws(ExportException::class, IOException::class)
    fun testExportValid1() {
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java
        )

        val codeIoVariables: List<CodeIoVariable> = Arrays.asList<CodeIoVariable>(
            CodeIoVariable(VariableCategory.INPUT, "INT", "Counter"),
            CodeIoVariable(VariableCategory.OUTPUT, "BOOL", "Active")
        )

        val typeContext = Arrays.asList<Type>(TypeInt.INT, TypeBool.BOOL)

        val testSpec: ConstraintSpecification =
            JsonTableParser.constraintTableFromJson(testjson)

        val result: ByteArrayOutputStream = exporter.export(testSpec)
        val resultString = IOUtils.toString(result.toByteArray(), "UTF-8")
        val expectedString = IOUtils.toString(
            this.javaClass.getResourceAsStream("spec_constraint_valid_1.xml"), "UTF-8"
        )
        Assert.assertEquals(
            TestUtils.removeWhitespace(expectedString),
            TestUtils.removeWhitespace(resultString)
        )
    }
}