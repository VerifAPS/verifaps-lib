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

    @Test
    public void testDontcare() throws RecognitionException {
        // - means TRUE
        Expression parsedExpr = parser.parseExpression("-");
        System.out.println("- <means> " + parsedExpr);
        assertEquals(
                literal(true),
                parsedExpr
        );
    }

    @Test
    public void testBoolConstant() throws RecognitionException {
        // TRUE means X = TRUE
        Expression parsedExpr = parser.parseExpression("TRUE");
        System.out.println("TRUE <means> " + parsedExpr);
        assertEquals(
                eq(var(cellName), literal(true)),
                parsedExpr
        );
    }

    @Test
    public void testIntConstant() throws RecognitionException {
        // 1 means X = 1
        Expression parsedExpr = parser.parseExpression("1");
        System.out.println("1 <means> " + parsedExpr);
        assertEquals(
                eq(var(cellName), literal(1)),
                parsedExpr
        );
    }

    @Test
    public void testOnesided() throws RecognitionException {
        // = 2+2 means X = 2 + 2
        Expression parsedExpr = parser.parseExpression("= 2+2");
        System.out.println("= 2+2 <means> " + parsedExpr);
        assertEquals(
                eq(var(cellName), plus(literal(2), literal(2))),
                parsedExpr
        );
    }
}
