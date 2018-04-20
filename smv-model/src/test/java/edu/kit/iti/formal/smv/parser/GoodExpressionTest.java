package edu.kit.iti.formal.smv.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
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


import edu.kit.iti.formal.smv.SMVPrinter;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;

@RunWith(Parameterized.class)
public class GoodExpressionTest {
    @Parameterized.Parameter
    public String testExpression;

    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getGoodExpressions() throws IOException {
        return TestHelper.loadLines("goodexpr.txt", 1);
    }

    @Test
    public void testParser() throws IOException {
        SMVParser slp = TestHelper.getParser(testExpression);
        SMVParser.ExprContext e = slp.expr();
        Assert.assertEquals(0, slp.getNumberOfSyntaxErrors());
        SMVExpr expr = (SMVExpr) e.accept(new SMVTransformToAST());
        String out = expr.accept(new SMVPrinter());
        System.out.println(">>> " + out);
    }

    @Test
    public void testLexer() {
        SMVLexer lex = new SMVLexer(CharStreams.fromString(testExpression));
        lex.getAllTokens().forEach(t -> {
            System.out.format("%6s: %-20s (%d,%d)%n",
                    lex.getVocabulary().getDisplayName(t.getType()),
                    t.getText(),
                    t.getLine(),
                    t.getCharPositionInLine());
        });
    }

    @Test
    public void testPrinter() {
        SMVParser slp1 = TestHelper.getParser(testExpression);
        SMVParser.ExprContext e1 = slp1.expr();
        SMVExpr expr1 = (SMVExpr) e1.accept(new SMVTransformToAST());
        String out1 = expr1.accept(new SMVPrinter());

        SMVParser slp2 = TestHelper.getParser(out1);
        SMVParser.ExprContext e2 = slp2.expr();
        SMVExpr expr2 = (SMVExpr) e2.accept(new SMVTransformToAST());
        String out2 = expr2.accept(new SMVPrinter());

        Assert.assertEquals(testExpression.replaceAll("[() ]",""),
                out2.replaceAll("[() ]",""));
        Assert.assertEquals(0, slp2.getNumberOfSyntaxErrors());
        Assert.assertEquals(out1, out2);
    }
}
