package edu.kit.iti.formal.stvs.logic.io.xml.verification

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade.importVerificationResult
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.expressions.ValueInt

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.verification.Counterexample
import edu.kit.iti.formal.stvs.model.verification.VerificationError
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess
import org.hamcrest.CoreMatchers
import org.junit.Assert
import org.junit.jupiter.api.Test
import java.io.File
import java.util.*

/**
 * @author Benjamin Alt
 */
class GeTeTaImporterTest {
    @Test
    @Throws(Exception::class)
    fun testDoImportCounterexample() {
        val typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL)
        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            File(
                StvsApplication::class.java.getResource(
                    "testSets/counterexample_1/constraint_spec_counterexample_valid_1.xml"
                ).toURI()
            ),
            ImporterFacade.ImportFormat.XML
        )
        val importer: GeTeTaImporter = GeTeTaImporter(typeContext, constraintSpec)
        val verificationResult: VerificationResult = importer.doImport(
            loadFromTestSets("/counterexample_1/geteta_report_counterexample_1.xml")
        )
        Assert.assertThat(
            verificationResult, CoreMatchers.instanceOf(
                Counterexample::class.java
            )
        )
        val counterexample = verificationResult as Counterexample
        Assert.assertEquals(ValueBool.TRUE, counterexample.counterexample.rows[0].cells["ONS_Trig"]!!.value)
        Assert.assertEquals(
            ValueInt(-10),
            counterexample.counterexample.getConcreteValuesForConstraintCell("neg_val", 0)[0]!!.value
        )
        Assert.assertEquals(3, counterexample.counterexample.columnHeaders.size.toLong())
        Assert.assertEquals(1, counterexample.counterexample.durations.size.toLong())
    }

    @Test
    @Throws(ImportException::class)
    fun testDoImportVerified() {
        val typeContext = Arrays.asList(
            TypeInt.INT, TypeBool.BOOL, enumOfName(
                "enumD", "literalOne", "literalTwo"
            )
        )
        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml"),
            ImporterFacade.ImportFormat.XML
        )
        val result: VerificationResult = GeTeTaImporter(typeContext, constraintSpec).doImport(
            loadFromTestSets("/valid_1/geteta_report_valid_1.xml")
        )
        Assert.assertThat(
            result, CoreMatchers.instanceOf(
                VerificationSuccess::class.java
            )
        )
    }

    @Test
    @Throws(ImportException::class)
    fun testDoImportUnknownStatus() {
        val typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL)
        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            StvsApplication::class.java.getResourceAsStream(
                "testSets/problematic_1/constraint_spec_unknown_error_1.xml"
            ),
            ImporterFacade.ImportFormat.XML
        )
        val result = importVerificationResult(
            loadFromTestSets("/problematic_1/geteta_report_unknown_error_1.xml"),
            ImporterFacade.ImportFormat.GETETA, typeContext, constraintSpec
        )
        Assert.assertThat(
            result, CoreMatchers.instanceOf(
                VerificationError::class.java
            )
        )
        assertNotEquals(Optional.empty(), result.logFile)
    }

    @Test(expected = ImportException::class)
    @Throws(ImportException::class)
    fun testDoImportInvalidXML() {
        val typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL)
        val result = importVerificationResult(
            this.javaClass
                .getResourceAsStream("report_illegal_xml_1.xml"), ImporterFacade.ImportFormat.GETETA,
            typeContext, ConstraintSpecification(FreeVariableList())
        )
    }
}