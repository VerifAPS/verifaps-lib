package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.StvsApplication
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
    private var hybridSpec: HybridSpecification? = null
    private val validSpec: ValidSpecification? = null
    private var concreteInstance: ConcreteSpecification? = null

    @BeforeEach
    fun setUp() {
        hybridSpec = ImporterFacade.importHybridSpec(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!
        )
        concreteInstance = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml")!!,
            listOf(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo")
            )
        )
    }

    @Test
    fun testGetCounterExample() {
        Assertions.assertEquals(Optional.empty<Any>(), hybridSpec!!.getCounterExample())
    }

    @Test
    fun testGetSetConcreteInstance() {
        Assertions.assertEquals(Optional.empty<Any>(), hybridSpec!!.getConcreteInstance())
        hybridSpec!!.setConcreteInstance(concreteInstance)
        Assertions.assertEquals(Optional.of(concreteInstance!!), hybridSpec!!.getConcreteInstance())
    }

    @Test
    fun testGetSetCounterExample() {
        Assertions.assertEquals(Optional.empty<Any>(), hybridSpec!!.getCounterExample())
        hybridSpec!!.setCounterExample(concreteInstance)
        Assertions.assertEquals(Optional.of(concreteInstance!!), hybridSpec!!.getCounterExample())
    }

    @Test
    fun testGetSetSelection() {
        Assertions.assertEquals(Selection(), hybridSpec!!.getSelection())
        hybridSpec!!.getSelection().setRow(3)
        hybridSpec!!.getSelection().setColumn("A")
        Assertions.assertEquals(Selection("A", 3), hybridSpec!!.getSelection())
    }

    @Test//(expected = IllegalArgumentException::class)
    fun testSetConcreteInstanceInvalid() {
        val badConcreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java.getResourceAsStream("spec_concrete_empty.xml")!!,
            listOf(TypeInt.INT, TypeBool.BOOL)
        )
        hybridSpec!!.setConcreteInstance(badConcreteSpec)
    }

    @Test
    fun testIsEditable() {
        Assertions.assertTrue(hybridSpec!!.isEditable)
    }

    @Test
    fun testRemoveConcreteInstance() {
        hybridSpec!!.setConcreteInstance(concreteInstance)
        Assertions.assertNotNull(hybridSpec!!.getConcreteInstance())
        hybridSpec!!.removeConcreteInstance()
        Assertions.assertNotNull(hybridSpec!!.getConcreteInstance())
    }

    @Test
    fun testEquals() {
        val identical: HybridSpecification = ImporterFacade.importHybridSpec(
            StvsApplication::class.java
                .getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml")!!
        )
        val identicalConcrete: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            StvsApplication::class.java.getResourceAsStream("testSets/valid_1/concrete_spec_valid_1.xml"),
            listOf(
                TypeInt.INT, TypeBool.BOOL,
                TypeFactory.enumOfName("enumD", "literalOne", "literalTwo")
            )
        )
        Assertions.assertEquals(hybridSpec, identical)
        hybridSpec!!.setConcreteInstance(concreteInstance)
        Assertions.assertNotEquals(hybridSpec, identical)
        identical.setConcreteInstance(identicalConcrete)
        Assertions.assertEquals(hybridSpec, identical)
        Assertions.assertNotEquals(hybridSpec, null)
        Assertions.assertEquals(hybridSpec, hybridSpec)
    }
}
