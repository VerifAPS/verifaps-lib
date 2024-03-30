package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import org.apache.commons.io.FileUtils
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.File
import java.util.*

/**
 * @author Benjamin Alt
 */
class XmlSessionImporterTest {
    @Test
    @Throws(Exception::class)
    fun testDoImportValid1() {
        val importedSession: StvsRootModel = ImporterFacade.importSession(
            File(
                StvsApplication::class.java
                    .getResource("testSets/valid_1/session_valid_with_concrete_instance_1.xml")!!.toURI().path
            ), GlobalConfig(), History()
        )
        val hybridSpec: HybridSpecification = ImporterFacade.importHybridSpec(
            File(StvsApplication::class.java.getResource("testSets/valid_1/constraint_spec_valid_1.xml")!!.toURI()),
        )
        val typeContext = listOf(TypeInt.INT, TypeBool.BOOL, enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            File(StvsApplication::class.java.getResource("testSets/valid_1/concrete_spec_valid_1.xml")!!.toURI()),
            typeContext
        )
        hybridSpec.concreteInstance = concreteSpec
        Assertions.assertEquals(hybridSpec, importedSession.hybridSpecifications[0])
        val code = FileUtils.readFileToString(
            File(
                StvsApplication::class.java.getResource("testSets/valid_1/code_valid_1.st")!!.toURI()
            ), "utf-8"
        )
        Assertions.assertEquals(
            TestUtils.removeWhitespace(code), TestUtils.removeWhitespace(
                importedSession.scenario
                    .code.sourcecode
            )
        )
    }
}