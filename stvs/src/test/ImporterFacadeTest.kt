package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecExporterTest
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import junit.framework.TestCase
import org.hamcrest.CoreMatchers
import org.junit.Assert
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
    @Throws(Exception::class)
    fun importConstraintSpecFile() {
        val file: File = File(
            XmlConcreteSpecExporterTest::class.java
                .getResource("spec_constraint_valid_1.xml").toURI().getPath()
        )
        val importedSpec = ImporterFacade.importConstraintSpec(file)
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java
        )

        val expectedSpec = JsonTableParser.constraintTableFromJson(testjson)
        TestCase.assertEquals(expectedSpec, importedSpec)
    }

    @Test(expected = ImportException::class)
    fun importConstraintSpecBadFormat() {
        val file = File(
            XmlConcreteSpecExporterTest::class.java
                .getResource("spec_constraint_valid_1.xml").toURI().getPath()
        )
        val importedSpec = ImporterFacade.importConstraintSpec(
            file
        )
    }

    @Test
    @Throws(Exception::class)
    fun importConcreteSpecFile() {
        val file: File =
            File(XmlConcreteSpecImporter::class.java.getResource("spec_concrete_valid_1.xml").toURI().getPath())
        val typeContext = Arrays.asList<Type>(TypeInt.INT, TypeBool.BOOL)
        val importedSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            file,
            ImporterFacade.ImportFormat.XML, typeContext
        )
        val json: JsonElement =
            JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val concreteSpec: ConcreteSpecification =
            JsonTableParser.concreteTableFromJson(emptyList<Type>(), false, json)
        TestCase.assertEquals(concreteSpec, importedSpec)
    }

    @Test(expected = ImportException::class)
    @Throws(URISyntaxException::class, IOException::class, ImportException::class)
    fun importConcreteSpecBadFormat() {
        val file: File = File(
            XmlConstraintSpecImporter::class.java
                .getResource("spec_concrete_valid_1.xml").toURI().getPath()
        )
        val importedSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            file,
            ImporterFacade.ImportFormat.GETETA
        )
    }

    @Test
    @Throws(Exception::class)
    fun importHybridSpecFile() {
        val file: File = File(
            XmlConstraintSpecImporter::class.java
                .getResource("spec_constraint_valid_1.xml").toURI().getPath()
        )
        val importedSpec: HybridSpecification = ImporterFacade.importHybridSpec(
            file,
            ImporterFacade.ImportFormat.XML
        )
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java
        )
        val expectedSpec: HybridSpecification = HybridSpecification(
            JsonTableParser.constraintTableFromJson(testjson), true
        )
        TestCase.assertEquals(expectedSpec, importedSpec)
    }

    @Test(expected = ImportException::class)
    @Throws(URISyntaxException::class, IOException::class, ImportException::class)
    fun importHybridSpecBadFormat() {
        val file: File = File(
            XmlConstraintSpecImporter::class.java
                .getResource("spec_constraint_valid_1.xml").toURI().getPath()
        )
        val importedSpec: HybridSpecification = ImporterFacade.importHybridSpec(
            file,
            ImporterFacade.ImportFormat.GETETA
        )
    }

    @Test
    @Throws(Exception::class)
    fun importConfigFile() {
        val file: File = File(
            this.javaClass.getResource(
                "/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default" +
                        ".xml"
            ).toURI()
        )
        val actualConfig: GlobalConfig = ImporterFacade.importConfig(file, ImporterFacade.ImportFormat.XML)
        val expectedConfig: GlobalConfig = GlobalConfig()

        //reset global config values
        expectedConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        expectedConfig.z3Path = "[Path to Z3 Executable]"
        Assert.assertEquals(expectedConfig, actualConfig)
    }

    @Test(expected = ImportException::class)
    @Throws(Exception::class)
    fun importConfigBadFormat() {
        val file: File = File(
            this.javaClass.getResource(
                "/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default" +
                        ".xml"
            ).toURI()
        )
        val actualConfig: GlobalConfig = ImporterFacade.importConfig(
            file, ImporterFacade.ImportFormat
                .GETETA
        )
    }

    @Test
    @Throws(Exception::class)
    fun importVerificationResult() {
        val typeContext =
            Arrays.asList<Type>(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
            ImporterFacade.ImportFormat.XML
        )
        val result: VerificationResult = ImporterFacade.importVerificationResult(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"), ImporterFacade
                .ImportFormat.GETETA, typeContext, constraintSpec
        )
        Assert.assertThat<VerificationResult>(
            result, CoreMatchers.instanceOf<VerificationResult>(
                VerificationSuccess::class.java
            )
        )
    }

    @Test(expected = ImportException::class)
    @Throws(Exception::class)
    fun importVerificationResultBadFormat() {
        val typeContext =
            Arrays.asList<Type>(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
            ImporterFacade.ImportFormat.XML
        )
        val result: VerificationResult = ImporterFacade.importVerificationResult(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"), ImporterFacade
                .ImportFormat.XML, typeContext, constraintSpec
        )
    }

    @Test
    @Throws(Exception::class)
    fun importSessionFile() {
        val importedSession: StvsRootModel = ImporterFacade.importSession(
            File(
                XmlSessionImporter::class.java
                    .getResource("session_valid_1.xml").toURI().getPath()
            ),
            ImporterFacade.ImportFormat.XML, GlobalConfig(), History()
        )
        val code: String = FileUtils.readFileToString(
            File(
                StvsApplication::class.java.getResource("testSets/valid_1/code_valid_1.st").toURI()
            ), "utf-8"
        )
        Assert.assertEquals(
            TestUtils.removeWhitespace(code), TestUtils.removeWhitespace(
                importedSession.scenario
                    .code.sourcecode
            )
        )
    }

    @Test(expected = ImportException::class)
    @Throws(Exception::class)
    fun importSessionBadFormat() {
        val importedSession: StvsRootModel = ImporterFacade.importSession(
            File(
                XmlSessionImporter::class.java
                    .getResource("session_valid_1.xml").toURI().getPath()
            ),
            ImporterFacade.ImportFormat.GETETA, GlobalConfig(), History()
        )
    }

    @Test
    @Throws(Exception::class)
    fun importStCode() {
        val file: File = File(StvsApplication::class.java.getResource("testSets/valid_1/code_valid_1.st").toURI())
        val expectedCode: String = FileUtils.readFileToString(file, "utf-8")
        val importedCode = ImporterFacade.importStCode(file)
        TestCase.assertEquals(
            TestUtils.removeWhitespace(expectedCode),
            TestUtils.removeWhitespace(importedCode.sourcecode)
        )
        TestCase.assertEquals(file.getAbsolutePath(), importedCode.filename)
    }

    @Test
    @Throws(Exception::class)
    fun importHistory() {
        val file: File = File(XmlSessionImporter::class.java.getResource("history_valid_1.xml").toURI())
        val history = ImporterFacade.importHistory(file, ImporterFacade.ImportFormat.XML)
        TestCase.assertEquals(
            "/home/bal/Projects/kit/pse/stverificationstudio/doc/" +
                    "FA-Testsession-Ressourcen/testsession_valid.xml", history.filenames[0]
        )
    }

    @Test
    @Throws(Exception::class)
    fun importFile() {
        val specFile: File = File(
            XmlConstraintSpecImporter::class.java.getResource(
                "spec_constraint_vali" +
                        "d_1.xml"
            ).toURI()
        )
        val codeFile: File = File(
            StvsApplication::class.java.getResource("testSets/valid_1/code_valid_1.st")
                .toURI()
        )
        val sessionFile: File = File(
            XmlSessionImporter::class.java.getResource("session_valid_1.xml")
                .toURI()
        )
        val testConfig: GlobalConfig = GlobalConfig()
        val testHistory = History()
        val specHandler = DummyHybridSpecificationHandler()
        val sessionHandler = DummyStvsRootModelHandler()
        val codeHandler = DummyCodeHandler()
        ImporterFacade.importFile(
            specFile, testConfig, testHistory, specHandler, sessionHandler,
            codeHandler
        )
        Assert.assertTrue(hybridSpecImported)
        TestCase.assertFalse(sessionImported)
        TestCase.assertFalse(codeImported)
        hybridSpecImported = false
        ImporterFacade.importFile(sessionFile, testConfig, testHistory, specHandler, sessionHandler, codeHandler)
        TestCase.assertFalse(hybridSpecImported)
        Assert.assertTrue(sessionImported)
        TestCase.assertFalse(codeImported)
        sessionImported = false
        ImporterFacade.importFile(codeFile, testConfig, testHistory, specHandler, sessionHandler, codeHandler)
        TestCase.assertFalse(hybridSpecImported)
        TestCase.assertFalse(sessionImported)
        Assert.assertTrue(codeImported)
    }

    private inner class DummyHybridSpecificationHandler : ImportHybridSpecificationHandler {
        override fun accept(hybridSpecification: HybridSpecification?) {
            hybridSpecImported = true
        }
    }

    private inner class DummyStvsRootModelHandler : ImportStvsRootModelHandler {
        override fun accept(model: StvsRootModel) {
            sessionImported = true
        }
    }

    private inner class DummyCodeHandler : ImportCodeHandler {
        override fun accept(code: Code?) {
            codeImported = true
        }
    }
}