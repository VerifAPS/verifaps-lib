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
 * You should have received a clone of the GNU General Public
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
    static IntegerPromotion ip = IntegerPromotion.Companion.getINSTANCE();


    Scope vd = new Scope();
    EnumerateType et = new EnumerateType("states", Arrays.asList("X", "Y", "Z"));

    @Before
    public void setup() {
        vd = new Scope();
        vd.add(new VariableDeclaration("a", DataTypes.INSTANCE.getUINT()));
        vd.add(new VariableDeclaration("b", DataTypes.INSTANCE.getINT()));
        vd.add(new VariableDeclaration("c", AnyBit.Companion.getBOOL()));
        vd.add(new VariableDeclaration("d", AnyBit.Companion.getBOOL()));
        vd.add(new VariableDeclaration("e", AnyBit.Companion.getBYTE()));
        vd.add(new VariableDeclaration("f", DataTypes.INSTANCE.getULINT()));
        vd.add(new VariableDeclaration("r", AnyReal.Companion.getREAL()));
        vd.add(new VariableDeclaration("q", AnyReal.Companion.getLREAL()));

        vd.add(new VariableDeclaration("s", IECString.Companion.getSTRING_16BIT()));

    }


    @Test
    public void testSignedInteger() {
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getLINT(), DataTypes.INSTANCE.getSINT()));
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getLINT(), DataTypes.INSTANCE.getINT()));
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getLINT(), DataTypes.INSTANCE.getDINT()));
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getSINT(), DataTypes.INSTANCE.getLINT()));
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getINT(), DataTypes.INSTANCE.getLINT()));
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getDINT(), DataTypes.INSTANCE.getLINT()));
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getLINT(), DataTypes.INSTANCE.getLINT()));


        assertEquals(DataTypes.INSTANCE.getSINT(), ip.getPromotion(DataTypes.INSTANCE.getSINT(), DataTypes.INSTANCE.getSINT()));
        assertEquals(DataTypes.INSTANCE.getINT(), ip.getPromotion(DataTypes.INSTANCE.getSINT(), DataTypes.INSTANCE.getINT()));
        assertEquals(DataTypes.INSTANCE.getDINT(), ip.getPromotion(DataTypes.INSTANCE.getSINT(), DataTypes.INSTANCE.getDINT()));

        assertEquals(DataTypes.INSTANCE.getINT(), ip.getPromotion(DataTypes.INSTANCE.getINT(), DataTypes.INSTANCE.getSINT()));
        assertEquals(DataTypes.INSTANCE.getINT(), ip.getPromotion(DataTypes.INSTANCE.getINT(), DataTypes.INSTANCE.getINT()));
        assertEquals(DataTypes.INSTANCE.getDINT(), ip.getPromotion(DataTypes.INSTANCE.getINT(), DataTypes.INSTANCE.getDINT()));
        assertEquals(DataTypes.INSTANCE.getLINT(), ip.getPromotion(DataTypes.INSTANCE.getINT(), DataTypes.INSTANCE.getLINT()));

    }

    @Test
    public void testUnSignedInteger() {
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(DataTypes.INSTANCE.getULINT(), INSTANCE.getUSINT()));
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(DataTypes.INSTANCE.getULINT(), DataTypes.INSTANCE.getUINT()));
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(DataTypes.INSTANCE.getULINT(), INSTANCE.getUDINT()));
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(INSTANCE.getUSINT(), DataTypes.INSTANCE.getULINT()));
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(DataTypes.INSTANCE.getUINT(), DataTypes.INSTANCE.getULINT()));
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(INSTANCE.getUDINT(), DataTypes.INSTANCE.getULINT()));
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(DataTypes.INSTANCE.getULINT(), DataTypes.INSTANCE.getULINT()));

        assertEquals(INSTANCE.getUSINT(), ip.getPromotion(INSTANCE.getUSINT(), INSTANCE.getUSINT()));
        assertEquals(DataTypes.INSTANCE.getUINT(), ip.getPromotion(INSTANCE.getUSINT(), DataTypes.INSTANCE.getUINT()));
        assertEquals(INSTANCE.getUDINT(), ip.getPromotion(INSTANCE.getUSINT(), INSTANCE.getUDINT()));

        assertEquals(DataTypes.INSTANCE.getUINT(), ip.getPromotion(DataTypes.INSTANCE.getUINT(), INSTANCE.getUSINT()));
        assertEquals(DataTypes.INSTANCE.getUINT(), ip.getPromotion(DataTypes.INSTANCE.getUINT(), DataTypes.INSTANCE.getUINT()));
        assertEquals(INSTANCE.getUDINT(), ip.getPromotion(DataTypes.INSTANCE.getUINT(), INSTANCE.getUDINT()));
        assertEquals(DataTypes.INSTANCE.getULINT(), ip.getPromotion(DataTypes.INSTANCE.getUINT(), DataTypes.INSTANCE.getULINT()));

    }


    @Test
    public void conversionInteger() {

    }


    @Test
    public void integerMixed() {
        IntegerPromotion ip = new IntegerPromotion();
        assertEquals(DataTypes.INSTANCE.getDINT(), ip.getPromotion(DataTypes.INSTANCE.getINT(), DataTypes.INSTANCE.getUINT()));
        assertEquals(DataTypes.INSTANCE.getDINT(), ip.getPromotion(DataTypes.INSTANCE.getUINT(), DataTypes.INSTANCE.getINT()));
    }


    @Test
    public void nonConformity() {
        assertEquals(null, ip.getPromotion(DataTypes.INSTANCE.getINT(), AnyBit.Companion.getWORD()));
    }

    @Test
    public void basicOperators() throws VariableNotDefinedException, TypeConformityException {
        assertDataType(DataTypes.INSTANCE.getDINT(), "-SINT#2 + UINT#2", null);
        assertDataType(DataTypes.INSTANCE.getLINT(), "-SINT#2 - LINT#2", null);
        assertDataType(DataTypes.INSTANCE.getSINT(), "-SINT#2", null);
        assertDataType(AnyBit.Companion.getBOOL(), "TRUE AND FALSE", null);
        assertDataType(AnyBit.Companion.getBOOL(), "NOT TRUE", null);
        assertDataType(AnyBit.Companion.getBOOL(), "NOT TRUE AND FALSE OR TRUE ", null);
        assertDataType(IECString.Companion.getSTRING_16BIT(), "s", vd);
        assertDataType(AnyBit.Companion.getBOOL(), "TRUE AND c", vd);
        assertDataType(AnyBit.Companion.getBOOL(), "d OR NOT c", vd);
        assertDataType(AnyReal.Companion.getREAL(), "a + b + r", vd);
        assertDataType(AnyReal.Companion.getLREAL(), "q -(a + b + r)", vd);
    }

    @Test
    public void functions() throws VariableNotDefinedException, TypeConformityException {
        //assertDataType(INT, "MAX(2,3)", null);
    }

    private void assertDataType(AnyDt dt, String sexpr, Scope vd) throws VariableNotDefinedException, TypeConformityException {
        assertEquals(dt, IEC61131Facade.INSTANCE.expr(sexpr).dataType(vd));
    }

    @Test(expected = VariableNotDefinedException.class)
    public void testVariableNotDefined() throws VariableNotDefinedException, TypeConformityException {
        assertDataType(AnyReal.Companion.getLREAL(), "LLLL", vd);
    }

    @Test(expected = TypeConformityException.class)
    public void typeMismatch() throws VariableNotDefinedException, TypeConformityException {
        assertDataType(AnyReal.Companion.getLREAL(), "TRUE + 2", vd);
    }

}
