package edu.kit.iti.formal.automation.datatypes

import org.junit.Assert.assertFalse
import org.junit.Assert.assertTrue
import org.junit.Test

/**
 * @author Alexander Weigl
 * @version 1 (04.02.19)
 */
class DataTypeAssignabilityTest {
    @Test
    fun visitIntegers() {
        assertTrue(INT.isAssignableTo(DINT))
        assertTrue(INT.isAssignableTo(INT))
        assertTrue(INT.isAssignableTo(LINT))
        assertTrue(SINT.isAssignableTo(DINT))
        assertTrue(SINT.isAssignableTo(INT))
        assertTrue(SINT.isAssignableTo(LINT))
        assertTrue(SINT.isAssignableTo(SINT))
        assertTrue(DINT.isAssignableTo(DINT))
        assertTrue(DINT.isAssignableTo(LINT))
        assertTrue(LINT.isAssignableTo(LINT))

        assertFalse(INT.isAssignableTo(SINT))
        assertFalse(DINT.isAssignableTo(SINT))
        assertFalse(DINT.isAssignableTo(INT))
        assertFalse(LINT.isAssignableTo(SINT))
        assertFalse(LINT.isAssignableTo(DINT))
        assertFalse(LINT.isAssignableTo(INT))
    }

    @Test
    fun visitBits() {
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.BOOL))
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.DWORD))
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.LWORD))
        assertTrue(AnyBit.BOOL.isAssignableTo(AnyBit.WORD))
        assertTrue(AnyBit.BOOL.isAssignableTo(INT))
        assertTrue(AnyBit.BOOL.isAssignableTo(SINT))
    }

    @Test
    fun visit2() {
    }

    @Test
    fun visit3() {
    }

    @Test
    fun visit4() {
    }

    @Test
    fun visit5() {
    }

    @Test
    fun visit6() {
    }

    @Test
    fun visit7() {
    }

    @Test
    fun visit8() {
    }

    @Test
    fun visit9() {
    }

    @Test
    fun visit10() {
    }
}