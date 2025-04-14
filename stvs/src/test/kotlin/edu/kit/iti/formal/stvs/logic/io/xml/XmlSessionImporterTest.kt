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
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class XmlSessionImporterTest {
    @Test
    fun testDoImportValid1() {
        val importedSession: StvsRootModel = ImporterFacade.importSession(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/session_valid_with_concrete_instance_1.xml")!!,
            GlobalConfig(), History()
        )
        val hybridSpec: HybridSpecification = ImporterFacade.importHybridSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!
        )

        val typeContext = listOf(TypeInt, TypeBool, enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml")!!,
            typeContext
        )
        hybridSpec.concreteInstance = concreteSpec
        Assertions.assertEquals(hybridSpec, importedSession.hybridSpecifications[0])
        val code =
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/code_valid_1.st")!!
                .reader().readText()

        Assertions.assertEquals(
            code.replace("\\s+".toRegex(), " ").trim(),
            importedSession.scenario.code.sourcecode.replace("\\s+".toRegex(), " ").trim()
        )
    }
}