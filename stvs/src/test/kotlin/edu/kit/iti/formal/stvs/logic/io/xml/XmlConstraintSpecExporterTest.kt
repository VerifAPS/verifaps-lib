package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationValidatorTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.apache.commons.io.IOUtils
import org.apache.commons.io.output.WriterOutputStream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.IOException
import java.io.StringWriter

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecExporterTest {
    private var exporter: XmlConstraintSpecExporter = XmlConstraintSpecExporter()

    @Test
    @Throws(ExportException::class, IOException::class)
    fun testExportValid1() {
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java
        )

        val codeIoVariables = listOf(
            CodeIoVariable(VariableCategory.INPUT, "INT", "Counter"),
            CodeIoVariable(VariableCategory.OUTPUT, "BOOL", "Active")
        )

        val typeContext = listOf(TypeInt.INT, TypeBool.BOOL)

        val testSpec = JsonTableParser.constraintTableFromJson(testjson)

        val result = StringWriter()
        exporter.export(testSpec, WriterOutputStream(result))
        val resultString = result.toString()
        val expectedString = IOUtils.toString(
            this.javaClass.getResourceAsStream("spec_constraint_valid_1.xml"), "UTF-8"
        )
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString))
    }
}