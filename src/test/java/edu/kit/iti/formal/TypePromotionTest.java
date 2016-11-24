package edu.kit.iti.formal;

import static edu.kit.iti.formal.automation.datatypes.AnyInt.UDINT;
import static edu.kit.iti.formal.automation.datatypes.AnyInt.USINT;
import static org.junit.Assert.*;
import static edu.kit.iti.formal.automation.datatypes.AnyInt.*;

import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.st.STUtil;
import edu.kit.iti.formal.automation.st.ast.Expression;
import org.junit.Test;

/**
 * Created by weigl on 15.11.16.
 */
public class TypePromotionTest {

    @Test
    public void testSignedInteger() {

        assertEquals(LINT, LINT.conformTo(SINT));
        assertEquals(LINT, LINT.conformTo(INT));
        assertEquals(LINT, LINT.conformTo(DINT));
        assertEquals(LINT, SINT.conformTo(LINT));
        assertEquals(LINT, INT.conformTo(LINT));
        assertEquals(LINT, DINT.conformTo(LINT));
        assertEquals(LINT, LINT.conformTo(LINT));


        assertEquals(SINT, SINT.conformTo(SINT));
        assertEquals(INT, SINT.conformTo(INT));
        assertEquals(DINT, SINT.conformTo(DINT));

        assertEquals(INT, INT.conformTo(SINT));
        assertEquals(INT, INT.conformTo(INT));
        assertEquals(DINT, INT.conformTo(DINT));
        assertEquals(LINT, INT.conformTo(LINT));

    }

    @Test
    public void testUnSignedInteger() {

        assertEquals(ULINT, ULINT.conformTo(USINT));
        assertEquals(ULINT, ULINT.conformTo(UINT));
        assertEquals(ULINT, ULINT.conformTo(UDINT));
        assertEquals(ULINT, USINT.conformTo(ULINT));
        assertEquals(ULINT, UINT.conformTo(ULINT));
        assertEquals(ULINT, UDINT.conformTo(ULINT));
        assertEquals(ULINT, ULINT.conformTo(ULINT));

        assertEquals(USINT, USINT.conformTo(USINT));
        assertEquals(UINT, USINT.conformTo(UINT));
        assertEquals(UDINT, USINT.conformTo(UDINT));

        assertEquals(UINT, UINT.conformTo(USINT));
        assertEquals(UINT, UINT.conformTo(UINT));
        assertEquals(UDINT, UINT.conformTo(UDINT));
        assertEquals(ULINT, UINT.conformTo(ULINT));

    }


    @Test
    public void conversionInteger() {

    }


    @Test public void integerMixed() {
        assertEquals(INT, INT.conformTo(UINT));
        assertEquals(INT, UINT.conformTo(INT));
    }


    @Test
    public void nonConformity() {
        assertEquals(null, INT.conformTo(AnyBit.WORD));
    }

    @Test
    public void basicOperators() {
        Expression a = STUtil.expr("-SINT#2 + UINT#2");
        System.out.println(a.dataType(null));
    }
}
