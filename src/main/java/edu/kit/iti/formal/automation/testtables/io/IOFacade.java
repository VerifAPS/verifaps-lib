/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables.io;


import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionLexer;
import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionParser;
import edu.kit.iti.formal.automation.testtables.model.Duration;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.schema.DataType;
import edu.kit.iti.formal.automation.testtables.schema.Variable;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

/**
 * Created by weigl on 10.12.16.
 */
public final class IOFacade {
    public static CellExpressionParser createParser(String input) {
        assert input != null;
        CellExpressionLexer lexer = new CellExpressionLexer(new ANTLRInputStream(input));
        lexer.removeErrorListeners();
        lexer.addErrorListener(ThrowingErrorListener.INSTANCE);

        CellExpressionParser parser = new CellExpressionParser(new CommonTokenStream(lexer));

        parser.removeErrorListeners();
        parser.addErrorListener(ThrowingErrorListener.INSTANCE);

        return parser;
    }

    /**
     * @param cell
     * @param column
     * @param vars
     * @return
     */
    public static SMVExpr parseCellExpression(String cell, SVariable column,
                                              GeneralizedTestTable vars) {
        assert cell != null;
        CellExpressionParser.CellContext p = createParser(cell).cell();
        ExprVisitor ev = new ExprVisitor(column, vars);
        SMVExpr expr = p.accept(ev);
        Report.debug("parsed: %s to %s", cell, expr);
        return expr;
    }

    public static Duration parseDuration(String duration) {
        if (duration.equalsIgnoreCase("omega")) {
            return Duration.OMEGA;
        }

        if (duration.equalsIgnoreCase("wait")) {
            return Duration.DET_WAIT;
        }


        CellExpressionParser parser = createParser(duration);
        CellExpressionParser.Fixed_intervalContext p = parser.fixed_interval();
        Duration d = new Duration();
        if (p.c != null) {
            int i = Integer.parseInt(p.c.getText());
            d.setLower(i);
            d.setUpper(i);
        } else if (p.dc != null) {
            d.setLower(0);
            d.setUpper(-1);
        } else {
            d.setLower(Integer.parseInt(p.a.getText()));
            if (p.inf != null)
                d.setUpper(-1);
            else
                d.setUpper(Integer.parseInt(p.b.getText()));
        }
        assert parser.getNumberOfSyntaxErrors() == 0;
        assert d.invariant();
        return d;
    }

    public static SVariable asSMVVariable(Variable column) {
        if (column == null) return null;
        SVariable v = new SVariable(column.getName(),
                getSMVDataType(column.getDataType()));
        return v;
    }

    private static SMVType getSMVDataType(DataType dataType) {
        return DataTypeTranslator.INSTANCE.apply(dataType);
    }
}
