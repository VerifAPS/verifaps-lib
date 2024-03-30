package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Benjamin Alt
 */
class HybridSpecificationTest {
    private lateinit var hybridSpec: HybridSpecification

    @BeforeEach
    fun before() {
        hybridSpec = ImporterFacade.importHybridSpec(loadFromTestSets("/valid_1/constraint_spec_valid_1.xml"))
    }

    private val concreteInstance = ImporterFacade.importConcreteSpec(
        loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"),
        listOf(
            TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo")
        )
    )

    @Test
    fun testcounterExample(){
        Assertions.assertEquals(null, hybridSpec.counterExample)
    }

    @Test
    fun testGetconcreteInstance() {
        Assertions.assertEquals(null, hybridSpec.concreteInstance)
        hybridSpec.concreteInstance = (concreteInstance)
        Assertions.assertEquals(Optional.of(concreteInstance), hybridSpec.concreteInstance)
    }

    @Test
    fun testGetcounterExample() {
        Assertions.assertEquals(null, hybridSpec.counterExample)
        hybridSpec.counterExample = (concreteInstance)
        Assertions.assertEquals(Optional.of(concreteInstance), hybridSpec.counterExample)
    }

    @Test
    fun testGetSetSelection() {
        Assertions.assertEquals(Selection(), hybridSpec.getSelection())
        hybridSpec.getSelection().row=(3)
        hybridSpec.getSelection().column=("A")
        Assertions.assertEquals(Selection("A", 3), hybridSpec.getSelection())
    }

    @Test//(expected = IllegalArgumentException::class)
    fun testconcreteInstanceInvalid() {
        val badConcreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java.getResourceAsStream("spec_concrete_empty.xml")!!,
            listOf(TypeInt.INT, TypeBool.BOOL)
        )
        hybridSpec.concreteInstance = (badConcreteSpec)
    }

    @Test
    fun testIsEditable() {
        Assertions.assertTrue(hybridSpec.isEditable)
    }

    @Test
    fun testRemoveConcreteInstance() {
        hybridSpec.concreteInstance = (concreteInstance)
        Assertions.assertNotNull(hybridSpec.concreteInstance)
        hybridSpec.removeConcreteInstance()
        Assertions.assertNotNull(hybridSpec.concreteInstance)
    }

    @Test
    fun testEquals() {
        val identical: HybridSpecification = ImporterFacade.importHybridSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml")
        )
        val identicalConcrete: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"),
            listOf(
                TypeInt.INT, TypeBool.BOOL,
                TypeFactory.enumOfName("enumD", "literalOne", "literalTwo")
            )
        )
        Assertions.assertEquals(hybridSpec, identical)
        hybridSpec.concreteInstance = concreteInstance
        Assertions.assertNotEquals(hybridSpec, identical)
        identical.concreteInstance = identicalConcrete
        Assertions.assertEquals(hybridSpec, identical)
        Assertions.assertNotEquals(hybridSpec, null)
        Assertions.assertEquals(hybridSpec, hybridSpec)
    }
}
