package edu.kit.iti.formal.automation.datatypes.promotion;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import static edu.kit.iti.formal.automation.datatypes.AnyInt.UDINT;
import static edu.kit.iti.formal.automation.datatypes.AnyInt.USINT;
import static org.junit.Assert.*;
import static edu.kit.iti.formal.automation.datatypes.AnyInt.*;

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.st.STUtil;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;

/**
 * Created by weigl on 15.11.16.
 */
public class TypePromotionTest {
    static IntegerPromotion ip = IntegerPromotion.INSTANCE;


    LocalScope vd = new LocalScope();
    EnumerateType et = new EnumerateType("states", Arrays.asList("X", "Y", "Z"));

    @Before
    public void setup() {
        vd = new LocalScope();
        vd.add(new VariableDeclaration("a", UINT));
        vd.add(new VariableDeclaration("b", INT));
        vd.add(new VariableDeclaration("c", AnyBit.BOOL));
        vd.add(new VariableDeclaration("d", AnyBit.BOOL));
        vd.add(new VariableDeclaration("e", AnyBit.BYTE));
        vd.add(new VariableDeclaration("f", ULINT));
        vd.add(new VariableDeclaration("r", AnyReal.REAL));
        vd.add(new VariableDeclaration("q", AnyReal.LREAL));

        vd.add(new VariableDeclaration("s", IECString.STRING_16BIT));

    }


    @Test
    public void testSignedInteger() {
        assertEquals(LINT, ip.getPromotion(LINT, SINT));
        assertEquals(LINT, ip.getPromotion(LINT, INT));
        assertEquals(LINT, ip.getPromotion(LINT, DINT));
        assertEquals(LINT, ip.getPromotion(SINT, LINT));
        assertEquals(LINT, ip.getPromotion(INT, LINT));
        assertEquals(LINT, ip.getPromotion(DINT, LINT));
        assertEquals(LINT, ip.getPromotion(LINT, LINT));


        assertEquals(SINT, ip.getPromotion(SINT, SINT));
        assertEquals(INT, ip.getPromotion(SINT, INT));
        assertEquals(DINT, ip.getPromotion(SINT, DINT));

        assertEquals(INT, ip.getPromotion(INT, SINT));
        assertEquals(INT, ip.getPromotion(INT, INT));
        assertEquals(DINT, ip.getPromotion(INT, DINT));
        assertEquals(LINT, ip.getPromotion(INT, LINT));

    }

    @Test
    public void testUnSignedInteger() {
        assertEquals(ULINT, ip.getPromotion(ULINT, USINT));
        assertEquals(ULINT, ip.getPromotion(ULINT, UINT));
        assertEquals(ULINT, ip.getPromotion(ULINT, UDINT));
        assertEquals(ULINT, ip.getPromotion(USINT, ULINT));
        assertEquals(ULINT, ip.getPromotion(UINT, ULINT));
        assertEquals(ULINT, ip.getPromotion(UDINT, ULINT));
        assertEquals(ULINT, ip.getPromotion(ULINT, ULINT));

        assertEquals(USINT, ip.getPromotion(USINT, USINT));
        assertEquals(UINT, ip.getPromotion(USINT, UINT));
        assertEquals(UDINT, ip.getPromotion(USINT, UDINT));

        assertEquals(UINT, ip.getPromotion(UINT, USINT));
        assertEquals(UINT, ip.getPromotion(UINT, UINT));
        assertEquals(UDINT, ip.getPromotion(UINT, UDINT));
        assertEquals(ULINT, ip.getPromotion(UINT, ULINT));

    }


    @Test
    public void conversionInteger() {

    }


    @Test
    public void integerMixed() {
        IntegerPromotion ip = new IntegerPromotion();
        assertEquals(INT, ip.getPromotion(INT, UINT));
        assertEquals(INT, ip.getPromotion(UINT, INT));
    }


    @Test
    public void nonConformity() {
        assertEquals(null, ip.getPromotion(INT, AnyBit.WORD));
    }

    @Test
    public void basicOperators() throws VariableNotDefinedException, TypeConformityException {
        assertDataType(INT, "-SINT#2 + UINT#2", null);
        assertDataType(LINT, "-SINT#2 - LINT#2", null);
        assertDataType(SINT, "-SINT#2", null);
        assertDataType(AnyBit.BOOL, "TRUE AND FALSE", null);
        assertDataType(AnyBit.BOOL, "NOT TRUE", null);
        assertDataType(AnyBit.BOOL, "NOT TRUE AND FALSE OR TRUE ", null);
        assertDataType(IECString.STRING_16BIT, "s", vd);
        assertDataType(AnyBit.BOOL, "TRUE AND c", vd);
        assertDataType(AnyBit.BOOL, "d OR NOT c", vd);
        assertDataType(AnyReal.REAL, "a + b + r", vd);
        assertDataType(AnyReal.LREAL, "q -(a + b + r)", vd);
    }

    @Test
    public void functions() throws VariableNotDefinedException, TypeConformityException {
        //assertDataType(INT, "MAX(2,3)", null);
    }

    private void assertDataType(Any dt, String sexpr, LocalScope vd) throws VariableNotDefinedException, TypeConformityException {
        assertEquals(dt, STUtil.expr(sexpr).dataType(vd));
    }

    @Test(expected = VariableNotDefinedException.class)
    public void testVariableNotDefined() throws VariableNotDefinedException, TypeConformityException {
        assertDataType(AnyReal.LREAL, "LLLL", vd);
    }

    @Test(expected = TypeConformityException.class)
    public void typeMismatch() throws VariableNotDefinedException, TypeConformityException {
        assertDataType(AnyReal.LREAL, "TRUE + 2", vd);
    }

}
