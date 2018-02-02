package edu.kit.iti.formal.automation.testtables.io;


import edu.kit.iti.formal.automation.testtables.exception.ProgramAbortionException;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.junit.Assert;
import org.junit.Test;

/**
 * Created by weigl on 15.12.16.
 */
public class CellExpressionAmbiguityTest {

    @Test
    public void testBoolean() {
        SVariable var = SVariable.create("a").asBool();
        Assert.assertEquals(
                SLiteral.TRUE.equal(var),
                parse("TRUE")
        );
    }


    public static SMVExpr parse(String cell) {

        SMVExpr smvExpr = IOFacade.parseCellExpression(cell, defaultVar(), CellExpressionTest.defaultTestTable());
        return smvExpr;
    }

    private static SVariable defaultVar() {
        SVariable var = SVariable.create("a").asBool();
        return var;
    }

    @Test
    public void testReference() {


        Assert.assertEquals(
                SVariable.create("b__history._$2").withUnsigned(16)
                        .equal(defaultVar()),
                parse("b[-2]")
        );
    }


    @Test(expected = ProgramAbortionException.class)
    public void testInvalidReferencePositive() {
        IOFacade.parseCellExpression("b[2]", SVariable.create("a").asBool(), CellExpressionTest.defaultTestTable());
    }


    @Test
    public void testValidReferenceZero() {
        IOFacade.parseCellExpression("b[0]", SVariable.create("a").asBool(), CellExpressionTest.defaultTestTable());
    }

}
