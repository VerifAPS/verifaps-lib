package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.apache.commons.io.IOUtils
import org.junit.Assert
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.io.IOException

/**
 * @author Benjamin Alt
 */
class XmlConcreteSpecExporterTest {
    private var exporter = XmlConcreteSpecExporter()

    @Test
    @Throws(
        ExportException::class, IOException::class, UnsupportedExpressionException::class, ParseException::class,
        ImportException::class
    )
    fun testExportConcreteValid1() {
        val json: JsonElement =
            JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val typeContext =
            listOf(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec =
            ImporterFacade.importConcreteSpec(loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"), typeContext)
        val result = TestUtils.stringOutputStream { exporter.export(concreteSpec, it) }
        val expectedString: String = IOUtils.toString(
            loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"),
            "UTF-8"
        )
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(result))
    }

    @Test
    @Throws(ExportException::class, IOException::class)
    fun testExportConcreteEmpty() {
        val concreteSpec = ConcreteSpecification(false)
        val result = TestUtils.stringOutputStream { exporter.export(concreteSpec, it) }
        val expectedString = IOUtils.toString(
            this.javaClass.getResourceAsStream("spec_concrete_empty.xml"), "UTF-8"
        )
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(result))
    }
}