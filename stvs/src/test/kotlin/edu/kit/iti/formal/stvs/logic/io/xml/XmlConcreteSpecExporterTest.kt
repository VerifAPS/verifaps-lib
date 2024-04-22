package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class XmlConcreteSpecExporterTest {
    private var exporter = XmlConcreteSpecExporter()

    @Test
    fun testExportConcreteValid1() {
        val json: JsonElement =
            JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val typeContext =
            listOf(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec =
            ImporterFacade.importConcreteSpec(loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"), typeContext)
        val result = TestUtils.stringOutputStream { exporter.export(concreteSpec, it) }
        val expectedString = loadFromTestSets("/valid_1/concrete_spec_valid_1.xml").reader().readText()
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(result))
    }

    @Test
    fun testExportConcreteEmpty() {
        val concreteSpec = ConcreteSpecification(false)
        val result = TestUtils.stringOutputStream { exporter.export(concreteSpec, it) }
        val expectedString = this.javaClass.getResourceAsStream("spec_concrete_empty.xml")!!.reader().readText()
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(result))
    }
}