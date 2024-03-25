package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import org.apache.commons.io.IOUtils
import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.util.*

/**
 * @author Benjamin Alt
 */
class XmlConcreteSpecExporterTest {
    private var exporter: XmlConcreteSpecExporter? = null

    @Before
    fun setUp() {
        exporter = XmlConcreteSpecExporter()
    }

    @Test
    @Throws(
        ExportException::class,
        IOException::class,
        UnsupportedExpressionException::class,
        ParseException::class,
        ImportException::class
    )
    fun testExportConcreteValid1() {
        val json: JsonElement =
            JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val typeContext =
            Arrays.asList<Type>(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml"), ImporterFacade
                .ImportFormat.XML, typeContext
        )
        val result: ByteArrayOutputStream = exporter.export(concreteSpec)
        val resultString = String(result.toByteArray(), charset("utf-8"))
        val expectedString: String = IOUtils.toString(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml"),
            "UTF-8"
        )
        Assert.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString))
    }

    @Test
    @Throws(ExportException::class, IOException::class)
    fun testExportConcreteEmpty() {
        val concreteSpec: ConcreteSpecification = ConcreteSpecification(false)
        val result: ByteArrayOutputStream = exporter.export(concreteSpec)
        val resultString = String(result.toByteArray(), charset("utf-8"))
        println(resultString)
        val expectedString = IOUtils.toString(
            this.javaClass.getResourceAsStream("spec_concrete_empty.xml"), "UTF-8"
        )
        Assert.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString))
    }
}