package edu.kit.iti.formal.stvs.model.expressions;

import org.antlr.v4.runtime.RecognitionException;
import org.junit.Test;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static edu.kit.iti.formal.stvs.model.expressions.SimpleExpressions.*;
import static org.junit.Assert.assertEquals;

/**
 * Created by philipp on 17.01.17.
 */
public class TestExpressionParser {

    // Initialize parser with context information:
    private final Set<Type> typeContext = new HashSet<>();
    private final Map<String, Type> variableContext = new HashMap<>();
    private final String cellName = "X";
    private final ExpressionParser parser = new ExpressionParser(cellName, typeContext, variableContext);

    public TestExpressionParser() {
        variableContext.put("constraintVar", TypeInt.INT);
    }

    private Expression assertParseExpressionEqual(String expr, Expression expected) {
        Expression parsedExpr = parser.parseExpression(expr);
        System.out.println(expr + " <means> " + parsedExpr);
        assertEquals(
                expected,
                parsedExpr
        );
        return parsedExpr;
    }

    @Test
    public void testDontcare() throws RecognitionException {
        // - means TRUE
        assertParseExpressionEqual("-", literal(true));
    }

    @Test
    public void testBoolConstant() throws RecognitionException {
        // TRUE means X = TRUE
        assertParseExpressionEqual("TRUE", equal(var(cellName), literal(true)));
    }

    @Test
    public void testIntConstant() throws RecognitionException {
        // 1 means X = 1
        assertParseExpressionEqual("1", equal(var(cellName), literal(1)));
    }

    @Test
    public void testOnesided() throws RecognitionException {
        // < 2 means X < 2
        assertParseExpressionEqual("< 2", lessThan(var(cellName), literal(2)));
    }

    @Test
    public void testPlus() throws RecognitionException {
        // = 2+2 means X = 2 + 2
        assertParseExpressionEqual("= 2+2",
                equal(var(cellName), plus(literal(2), literal(2)))
        );
    }

    // TODO: Write Implementations for not-to-be-supported grammar rules, like
    // - stvs functions
    // - 'guarded commands' i.e. ifs
    // TODO: Implement intervals!

}
