package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class XmlConcreteSpecImporterTest {
    private var importer = XmlConcreteSpecImporter(listOf(TypeInt, TypeBool))

    @Test
    @Throws(Exception::class)
    fun testDoImportValid1() {
        val importedSpec = importer.doImport(javaClass.getResourceAsStream("spec_concrete_valid_1.xml")!!)
        val json = JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val concreteSpec = JsonTableParser.concreteTableFromJson(emptyList(), false, json)
        Assertions.assertEquals(concreteSpec, importedSpec)
    }

    @Test
    @Throws(ImportException::class)
    fun testDoImportEmpty() {
        val importedSpec: ConcreteSpecification =
            importer.doImport(javaClass.getResourceAsStream("spec_concrete_empty.xml")!!)
        Assertions.assertEquals(ConcreteSpecification(false), importedSpec)
    }

    @Test//(expected = ImportException::class)
    @Throws(ImportException::class)
    fun testDoImportInvalidXml() {
        assertFailsWith<ImportException> {
            importer.doImport(javaClass.getResourceAsStream("spec_concrete_invalid_xml_1.xml")!!)
        }
    }

    @Test//(expected = ImportException::class)
    @Throws(ImportException::class)
    fun testDoImportInvalidData() {
        assertFailsWith<ImportException> {
            importer.doImport(javaClass.getResourceAsStream("spec_concrete_invalid_data_1.xml")!!)
        }
    }
}