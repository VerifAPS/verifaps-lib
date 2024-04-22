package edu.kit.iti.formal.stvs.logic.io

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.xml.*
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.*
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import java.io.File
import java.util.*

/**
 * @author Benjamin Alt
 */
class ImporterFacadeTest {
    private var hybridSpecImported = false
    private var sessionImported = false
    private var codeImported = false

    @Test
    fun importConstraintSpecFile() {
        val file = XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_constraint_valid_1.xml")!!
        val importedSpec = ImporterFacade.importConstraintSpec(file)
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java
        )

        val expectedSpec = JsonTableParser.constraintTableFromJson(testjson)
        assertEquals(expectedSpec, importedSpec)
    }

    @Test
    fun importConstraintSpecBadFormat() {
        val file = XmlConcreteSpecExporterTest::class.java.getResourceAsStream("spec_constraint_valid_1.xml")!!
        ImporterFacade.importConstraintSpec(file)
    }

    @Test
    fun importConcreteSpecFile() {
        val file = XmlConcreteSpecImporter::class.java.getResourceAsStream("spec_concrete_valid_1.xml")!!
        val typeContext = listOf(TypeInt.INT, TypeBool.BOOL)
        val importedSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(file, typeContext)
        val json: JsonElement =
            JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val concreteSpec = JsonTableParser.concreteTableFromJson(emptyList(), false, json)
        assertEquals(concreteSpec, importedSpec)
    }

    @Test
    @Throws(Exception::class)
    fun importHybridSpecFile() {
        val file = XmlConstraintSpecImporter::class.java.getResourceAsStream("spec_constraint_valid_1.xml")!!
        val importedSpec: HybridSpecification = ImporterFacade.importHybridSpec(file)
        val testJson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json", ConstraintSpecificationValidatorTest::class.java
        )
        val expectedSpec = HybridSpecification(
            JsonTableParser.constraintTableFromJson(testJson), true
        )
        assertEquals(expectedSpec, importedSpec)
    }

    @Test
    fun importConfigFile() {
        val file = File(
            this.javaClass.getResource(
                "/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default.xml"
            )!!.toURI()
        )
        val actualConfig = ImporterFacade.importConfig(file)
        val expectedConfig = GlobalConfig()

        //reset global config values
        expectedConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        expectedConfig.z3Path = "[Path to Z3 Executable]"
        assertEquals(expectedConfig, actualConfig)
    }

    @Test
    @Disabled
    fun importVerificationResult() {
        val typeContext =
            listOf(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml")
        )
        val result: VerificationResult = ImporterFacade.importVerificationResult(
            loadFromTestSets("/valid_1/geteta_report_valid_1.xml"), typeContext, constraintSpec
        )
        assertTrue(result is VerificationSuccess)
    }

    @Test//(expected = ImportException::class)
    @Disabled
    fun importVerificationResultBadFormat() {
        val typeContext =
            listOf(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val constraintSpec: ConstraintSpecification =
            ImporterFacade.importConstraintSpec(loadFromTestSets("/valid_1/constraint_spec_valid_1.xml"))
        ImporterFacade.importVerificationResult(
            loadFromTestSets("/valid_1/geteta_report_valid_1.xml"), typeContext, constraintSpec
        )
    }

    @Test
    fun importSessionFile() {
        val importedSession: StvsRootModel = ImporterFacade.importSession(
            XmlSessionImporter::class.java.getResourceAsStream("session_valid_1.xml")!!,
            GlobalConfig(), History()
        )
        val code = StvsApplication::class.java.getResourceAsStream("testSets/valid_1/code_valid_1.st")!!
            .bufferedReader().readText()

        assertEquals(
            code.replace("\\s+".toRegex(), " "),
            importedSession.scenario.code.sourcecode.replace("\\s+".toRegex(), " ")
        )
    }

    @Test
    fun importStCode() {
        val file = File(StvsApplication::class.java.getResource("testSets/valid_1/code_valid_1.st")!!.toURI())
        val expectedCode: String = file.readText()
        val importedCode = ImporterFacade.importStCode(file)
        assertEquals(
            TestUtils.removeWhitespace(expectedCode),
            TestUtils.removeWhitespace(importedCode.sourcecode)
        )
        assertEquals(file.absolutePath, importedCode.filename)
    }

    @Test
    fun importHistory() {
        val file = File(XmlSessionImporter::class.java.getResource("history_valid_1.xml")!!.toURI())
        val history = ImporterFacade.importHistory(file)
        assertEquals(
            "/home/bal/Projects/kit/pse/stverificationstudio/doc/FA-Testsession-Ressourcen/testsession_valid.xml",
            history.filenames[0]
        )
    }

    @Test
    fun importFile() {
        val specFile = File(
            XmlConstraintSpecImporter::class.java.getResource("spec_constraint_valid_1.xml")!!.toURI()
        )
        val codeFile = File(
            StvsApplication::class.java.getResource("testSets/valid_1/code_valid_1.st")!!.toURI()
        )
        val sessionFile = File(
            XmlSessionImporter::class.java.getResource("session_valid_1.xml")!!
                .toURI()
        )
        val testConfig = GlobalConfig()
        val testHistory = History()
        val specHandler = DummyHybridSpecificationHandler()
        val sessionHandler = DummyStvsRootModelHandler()
        val codeHandler = DummyCodeHandler()
        ImporterFacade.importFile(
            specFile, testConfig, testHistory, specHandler, sessionHandler,
            codeHandler
        )
        assertTrue(hybridSpecImported)
        assertFalse(sessionImported)
        assertFalse(codeImported)
        hybridSpecImported = false
        ImporterFacade.importFile(sessionFile, testConfig, testHistory, specHandler, sessionHandler, codeHandler)
        assertFalse(hybridSpecImported)
        assertTrue(sessionImported)
        assertFalse(codeImported)
        sessionImported = false
        ImporterFacade.importFile(codeFile, testConfig, testHistory, specHandler, sessionHandler, codeHandler)
        assertFalse(hybridSpecImported)
        assertFalse(sessionImported)
        assertTrue(codeImported)
    }

    private inner class DummyHybridSpecificationHandler : ImportHybridSpecificationHandler {
        override fun accept(hybridSpecification: HybridSpecification) {
            hybridSpecImported = true
        }
    }

    private inner class DummyStvsRootModelHandler : ImportStvsRootModelHandler {
        override fun accept(model: StvsRootModel) {
            sessionImported = true
        }
    }

    private inner class DummyCodeHandler : ImportCodeHandler {
        override fun accept(code: Code) {
            codeImported = true
        }
    }
}