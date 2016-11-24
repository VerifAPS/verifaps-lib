package edu.kit.iti.formal;

import static edu.kit.iti.formal.automation.datatypes.AnyInt.UDINT;
import static edu.kit.iti.formal.automation.datatypes.AnyInt.USINT;
import static org.junit.Assert.*;
import static edu.kit.iti.formal.automation.datatypes.AnyInt.*;

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.datatypes.promotion.IntegerPromotion;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedinScope;
import edu.kit.iti.formal.automation.st.STUtil;
import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import org.junit.Before;
import org.junit.Test;

/**
 * Created by weigl on 15.11.16.
 */
public class TypePromotionTest {
    static IntegerPromotion ip = IntegerPromotion.INSTANCE;


    LocalScope vd = new LocalScope();
    EnumerateType et = new EnumerateType("states", new String[]{"X", "Y", "Z"});

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
    public void basicOperators() throws VariableNotDefinedinScope, TypeConformityException {
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
    public void functions() throws VariableNotDefinedinScope, TypeConformityException {
        assertDataType(INT, "MAX(2,3)", null);
    }

    private void assertDataType(Any dt, String sexpr, LocalScope vd) throws VariableNotDefinedinScope, TypeConformityException {
        assertEquals(dt, STUtil.expr(sexpr).dataType(vd));
    }

    @Test(expected = VariableNotDefinedinScope.class)
    public void testVariableNotDefined() throws VariableNotDefinedinScope, TypeConformityException {
        assertDataType(AnyReal.LREAL, "LLLL", vd);
    }

    @Test(expected = TypeConformityException.class)
    public void typeMismatch() throws VariableNotDefinedinScope, TypeConformityException {
        assertDataType(AnyReal.LREAL, "TRUE + 2", vd);
    }

}