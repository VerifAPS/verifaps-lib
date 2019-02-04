package edu.kit.iti.formal.automation.datatypes.promotion


import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.exceptions.TypeConformityException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import org.junit.Assert.assertEquals
import org.junit.Before
import org.junit.Test
import java.util.*

/**
 * Created by weigl on 15.11.16.
 */
class TypePromotionTest {
    internal var vd = Scope()
    internal var et = EnumerateType("states", Arrays.asList("X", "Y", "Z"))

    @Before
    fun setup() {
        vd = Scope()
        vd.add(VariableDeclaration("a", UINT))
        vd.add(VariableDeclaration("b", INT))
        vd.add(VariableDeclaration("c", AnyBit.BOOL))
        vd.add(VariableDeclaration("d", AnyBit.BOOL))
        vd.add(VariableDeclaration("e", AnyBit.BYTE))
        vd.add(VariableDeclaration("f", ULINT))
        vd.add(VariableDeclaration("r", AnyReal.REAL))
        vd.add(VariableDeclaration("q", AnyReal.LREAL))

        vd.add(VariableDeclaration("s", IECString.STRING))

    }


    @Test
    fun testSignedInteger() {
        assertEquals(LINT, LINT promoteWith SINT)
        assertEquals(LINT, LINT promoteWith INT)
        assertEquals(LINT, LINT promoteWith DINT)
        assertEquals(LINT, SINT promoteWith LINT)
        assertEquals(LINT, INT promoteWith LINT)
        assertEquals(LINT, DINT promoteWith LINT)
        assertEquals(LINT, LINT promoteWith LINT)


        assertEquals(SINT, SINT promoteWith SINT)
        assertEquals(INT, SINT promoteWith INT)
        assertEquals(DINT, SINT promoteWith DINT)

        assertEquals(INT, INT promoteWith SINT)
        assertEquals(INT, INT promoteWith INT)
        assertEquals(DINT, INT promoteWith DINT)
        assertEquals(LINT, INT promoteWith LINT)

    }

    @Test
    fun testUnSignedInteger() {
        assertEquals(ULINT, ULINT promoteWith USINT)
        assertEquals(ULINT, ULINT promoteWith UINT)
        assertEquals(ULINT, ULINT promoteWith UDINT)
        assertEquals(ULINT, USINT promoteWith ULINT)
        assertEquals(ULINT, UINT promoteWith ULINT)
        assertEquals(ULINT, UDINT promoteWith ULINT)
        assertEquals(ULINT, ULINT promoteWith ULINT)

        assertEquals(USINT, USINT promoteWith USINT)
        assertEquals(UINT, USINT promoteWith UINT)
        assertEquals(UDINT, USINT promoteWith UDINT)

        assertEquals(UINT, UINT promoteWith USINT)
        assertEquals(UINT, UINT promoteWith UINT)
        assertEquals(UDINT, UINT promoteWith UDINT)
        assertEquals(ULINT, UINT promoteWith ULINT)

    }


    @Test
    fun conversionInteger() {

    }


    @Test
    fun integerMixed() {
        assertEquals(DINT, INT promoteWith UINT)
        assertEquals(DINT, UINT promoteWith INT)
    }


    @Test
    fun nonConformity() {
        assertEquals(null, INT promoteWith AnyBit.WORD)
    }

    @Test
    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    fun basicOperators() {
        assertDataType(SINT, "-SINT#2")
        assertDataType(DINT, "-UINT#2")
        assertDataType(UINT, "UINT#2")

        assertDataType(DINT, "-SINT#2 + UINT#2")
        assertDataType(LINT, "-SINT#2 - LINT#2")
        assertDataType(SINT, "-SINT#2")
        assertDataType(AnyBit.BOOL, "TRUE AND FALSE")
        assertDataType(AnyBit.BOOL, "NOT TRUE")
        assertDataType(AnyBit.BOOL, "NOT TRUE AND FALSE OR TRUE ")
        assertDataType(IECString.STRING, "s", vd)
        assertDataType(AnyBit.BOOL, "TRUE AND c", vd)
        assertDataType(AnyBit.BOOL, "d OR NOT c", vd)
        assertDataType(AnyReal.REAL, "a + b + r", vd)
        assertDataType(AnyReal.LREAL, "q -(a + b + r)", vd)
    }

    @Test
    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    fun functions() {
        //assertDataType(INT, "MAX(2,3)", null);
    }

    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    private fun assertDataType(dt: AnyDt?, sexpr: String, scope: Scope = vd) {
        assertEquals(dt, IEC61131Facade.expr(sexpr).dataType(scope))
    }

    @Test(expected = VariableNotDefinedException::class)
    @Throws(VariableNotDefinedException::class, TypeConformityException::class)

    fun testVariableNotDefined() {
        assertDataType(AnyReal.LREAL, "LLLL", vd)
    }

    @Test(expected = TypeConformityException::class)
    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    fun typeMismatch() {
        assertDataType(AnyReal.LREAL, "TRUE + INT#2", vd)
    }
}
