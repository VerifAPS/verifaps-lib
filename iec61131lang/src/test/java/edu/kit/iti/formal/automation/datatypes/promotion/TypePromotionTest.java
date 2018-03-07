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

import static edu.kit.iti.formal.automation.datatypes.DataTypes.UDINT;
import static edu.kit.iti.formal.automation.datatypes.DataTypes.USINT;
import static org.junit.Assert.*;

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;

/**
 * Created by weigl on 15.11.16.
 */
public class TypePromotionTest {
    static IntegerPromotion ip = IntegerPromotion.INSTANCE;


    Scope vd = new Scope();
    EnumerateType et = new EnumerateType("states", Arrays.asList("X", "Y", "Z"));

    @Before
    public void setup() {
        vd = new Scope();
        vd.add(new VariableDeclaration("a", DataTypes.UINT));
        vd.add(new VariableDeclaration("b", DataTypes.INT));
        vd.add(new VariableDeclaration("c", AnyBit.BOOL));
        vd.add(new VariableDeclaration("d", AnyBit.BOOL));
        vd.add(new VariableDeclaration("e", AnyBit.BYTE));
        vd.add(new VariableDeclaration("f", DataTypes.ULINT));
        vd.add(new VariableDeclaration("r", AnyReal.REAL));
        vd.add(new VariableDeclaration("q", AnyReal.LREAL));

        vd.add(new VariableDeclaration("s", IECString.STRING_16BIT));

    }


    @Test
    public void testSignedInteger() {
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.LINT, DataTypes.SINT));
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.LINT, DataTypes.INT));
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.LINT, DataTypes.DINT));
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.SINT, DataTypes.LINT));
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.INT, DataTypes.LINT));
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.DINT, DataTypes.LINT));
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.LINT, DataTypes.LINT));


        assertEquals(DataTypes.SINT, ip.getPromotion(DataTypes.SINT, DataTypes.SINT));
        assertEquals(DataTypes.INT, ip.getPromotion(DataTypes.SINT, DataTypes.INT));
        assertEquals(DataTypes.DINT, ip.getPromotion(DataTypes.SINT, DataTypes.DINT));

        assertEquals(DataTypes.INT, ip.getPromotion(DataTypes.INT, DataTypes.SINT));
        assertEquals(DataTypes.INT, ip.getPromotion(DataTypes.INT, DataTypes.INT));
        assertEquals(DataTypes.DINT, ip.getPromotion(DataTypes.INT, DataTypes.DINT));
        assertEquals(DataTypes.LINT, ip.getPromotion(DataTypes.INT, DataTypes.LINT));

    }

    @Test
    public void testUnSignedInteger() {
        assertEquals(DataTypes.ULINT, ip.getPromotion(DataTypes.ULINT, USINT));
        assertEquals(DataTypes.ULINT, ip.getPromotion(DataTypes.ULINT, DataTypes.UINT));
        assertEquals(DataTypes.ULINT, ip.getPromotion(DataTypes.ULINT, UDINT));
        assertEquals(DataTypes.ULINT, ip.getPromotion(USINT, DataTypes.ULINT));
        assertEquals(DataTypes.ULINT, ip.getPromotion(DataTypes.UINT, DataTypes.ULINT));
        assertEquals(DataTypes.ULINT, ip.getPromotion(UDINT, DataTypes.ULINT));
        assertEquals(DataTypes.ULINT, ip.getPromotion(DataTypes.ULINT, DataTypes.ULINT));

        assertEquals(USINT, ip.getPromotion(USINT, USINT));
        assertEquals(DataTypes.UINT, ip.getPromotion(USINT, DataTypes.UINT));
        assertEquals(UDINT, ip.getPromotion(USINT, UDINT));

        assertEquals(DataTypes.UINT, ip.getPromotion(DataTypes.UINT, USINT));
        assertEquals(DataTypes.UINT, ip.getPromotion(DataTypes.UINT, DataTypes.UINT));
        assertEquals(UDINT, ip.getPromotion(DataTypes.UINT, UDINT));
        assertEquals(DataTypes.ULINT, ip.getPromotion(DataTypes.UINT, DataTypes.ULINT));

    }


    @Test
    public void conversionInteger() {

    }


    @Test
    public void integerMixed() {
        IntegerPromotion ip = new IntegerPromotion();
        assertEquals(DataTypes.DINT, ip.getPromotion(DataTypes.INT, DataTypes.UINT));
        assertEquals(DataTypes.DINT, ip.getPromotion(DataTypes.UINT, DataTypes.INT));
    }


    @Test
    public void nonConformity() {
        assertEquals(null, ip.getPromotion(DataTypes.INT, AnyBit.WORD));
    }

    @Test
    public void basicOperators() throws VariableNotDefinedException, TypeConformityException {
        assertDataType(DataTypes.DINT, "-SINT#2 + UINT#2", null);
        assertDataType(DataTypes.LINT, "-SINT#2 - LINT#2", null);
        assertDataType(DataTypes.SINT, "-SINT#2", null);
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

    private void assertDataType(AnyDt dt, String sexpr, Scope vd) throws VariableNotDefinedException, TypeConformityException {
        assertEquals(dt, IEC61131Facade.expr(sexpr).dataType(vd));
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
