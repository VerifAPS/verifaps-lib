package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationValidatorTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import junit.framework.TestCase
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.File
import java.io.FileInputStream

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecImporterTest {
    private var importer = XmlConstraintSpecImporter()

    @Test
    @Throws(Exception::class)
    fun testDoImportValid1() {
        val inputStream = this.javaClass.getResourceAsStream("spec_constraint_valid_1.xml")!!
        val importedSpec: ConstraintSpecification = importer.doImport(inputStream)
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java
        )

        val expectedSpec: ConstraintSpecification =
            JsonTableParser.constraintTableFromJson(testjson)
        Assertions.assertEquals(expectedSpec, importedSpec)
    }

    @Test
    @Throws(Exception::class)
    fun testDoImportValidEnum1() {
        val inputStream: FileInputStream =
            FileInputStream(File(this.javaClass.getResource("spec_constraint_valid_enum_1.xml").toURI()))
        val importedSpec: ConstraintSpecification = importer.doImport(inputStream)
        println()
    }
}