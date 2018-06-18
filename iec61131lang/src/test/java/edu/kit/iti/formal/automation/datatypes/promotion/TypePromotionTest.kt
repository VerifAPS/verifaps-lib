package edu.kit.iti.formal.automation.datatypes.promotion

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

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
        assertEquals(LINT, ip.getPromotion(LINT, SINT))
        assertEquals(LINT, ip.getPromotion(LINT, INT))
        assertEquals(LINT, ip.getPromotion(LINT, DINT))
        assertEquals(LINT, ip.getPromotion(SINT, LINT))
        assertEquals(LINT, ip.getPromotion(INT, LINT))
        assertEquals(LINT, ip.getPromotion(DINT, LINT))
        assertEquals(LINT, ip.getPromotion(LINT, LINT))


        assertEquals(SINT, ip.getPromotion(SINT, SINT))
        assertEquals(INT, ip.getPromotion(SINT, INT))
        assertEquals(DINT, ip.getPromotion(SINT, DINT))

        assertEquals(INT, ip.getPromotion(INT, SINT))
        assertEquals(INT, ip.getPromotion(INT, INT))
        assertEquals(DINT, ip.getPromotion(INT, DINT))
        assertEquals(LINT, ip.getPromotion(INT, LINT))

    }

    @Test
    fun testUnSignedInteger() {
        assertEquals(ULINT, ip.getPromotion(ULINT, USINT))
        assertEquals(ULINT, ip.getPromotion(ULINT, UINT))
        assertEquals(ULINT, ip.getPromotion(ULINT, UDINT))
        assertEquals(ULINT, ip.getPromotion(USINT, ULINT))
        assertEquals(ULINT, ip.getPromotion(UINT, ULINT))
        assertEquals(ULINT, ip.getPromotion(UDINT, ULINT))
        assertEquals(ULINT, ip.getPromotion(ULINT, ULINT))

        assertEquals(USINT, ip.getPromotion(USINT, USINT))
        assertEquals(UINT, ip.getPromotion(USINT, UINT))
        assertEquals(UDINT, ip.getPromotion(USINT, UDINT))

        assertEquals(UINT, ip.getPromotion(UINT, USINT))
        assertEquals(UINT, ip.getPromotion(UINT, UINT))
        assertEquals(UDINT, ip.getPromotion(UINT, UDINT))
        assertEquals(ULINT, ip.getPromotion(UINT, ULINT))

    }


    @Test
    fun conversionInteger() {

    }


    @Test
    fun integerMixed() {
        val ip = IntegerPromotion()
        assertEquals(DINT, ip.getPromotion(INT, UINT))
        assertEquals(DINT, ip.getPromotion(UINT, INT))
    }


    @Test
    fun nonConformity() {
        assertEquals(null, ip.getPromotion(INT, AnyBit.WORD))
    }

    @Test
    @Throws(VariableNotDefinedException::class, TypeConformityException::class)
    fun basicOperators() {
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
        assertDataType(AnyReal.LREAL, "TRUE + 2", vd)
    }

    companion object {
        internal var ip = IntegerPromotion.INSTANCE
    }

}
