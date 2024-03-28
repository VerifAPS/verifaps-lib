package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.model.expressions.Type
import junit.framework.TestCase
import org.junit.Before
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Benjamin Alt
 */
class XmlConcreteSpecImporterTest {
    private var importer: XmlConcreteSpecImporter? = null

    @Before
    @Throws(ImportException::class)
    fun setUp() {
        importer = XmlConcreteSpecImporter(Arrays.asList(TypeInt.INT, TypeBool.BOOL))
    }

    @Test
    @Throws(Exception::class)
    fun testDoImportValid1() {
        val importedSpec: ConcreteSpecification = importer.doImport(
            javaClass.getResourceAsStream("spec_concrete_valid_1.xml")
        )
        val json: JsonElement =
            JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val concreteSpec: ConcreteSpecification =
            JsonTableParser.concreteTableFromJson(emptyList<Type>(), false, json)
        TestCase.assertEquals(concreteSpec, importedSpec)
    }

    @Test
    @Throws(ImportException::class)
    fun testDoImportEmpty() {
        val importedSpec: ConcreteSpecification = importer.doImport(
            javaClass.getResourceAsStream("spec_concrete_empty.xml")
        )
        TestCase.assertEquals(ConcreteSpecification(false), importedSpec)
    }

    @Test(expected = ImportException::class)
    @Throws(ImportException::class)
    fun testDoImportInvalidXml() {
        val importedSpec: ConcreteSpecification = importer.doImport(
            javaClass.getResourceAsStream("spec_concrete_invalid_xml_1.xml")
        )
    }

    @Test(expected = ImportException::class)
    @Throws(ImportException::class)
    fun testDoImportInvalidData() {
        val importedSpec: ConcreteSpecification = importer.doImport(
            javaClass.getResourceAsStream("spec_concrete_invalid_data_1.xml")
        )
    }
}