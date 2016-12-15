package edu.kit.iti.formal.exteta.io;

import edu.kit.iti.formal.exteta.grammar.CellExpressionLexer;
import edu.kit.iti.formal.exteta.grammar.CellExpressionParser;
import edu.kit.iti.formal.exteta.model.Duration;
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.exteta.schema.DataType;
import edu.kit.iti.formal.exteta.schema.Variable;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;

/**
 * Created by weigl on 10.12.16.
 */
public final class IOFacade {
    public static CellExpressionParser createParser(String input) {
        CellExpressionLexer lexer = new CellExpressionLexer(new ANTLRInputStream(input));
        lexer.removeErrorListeners();
        lexer.addErrorListener(ThrowingErrorListener.INSTANCE);

        CellExpressionParser parser = new CellExpressionParser(new CommonTokenStream(lexer));

        parser.removeErrorListeners();
        parser.addErrorListener(ThrowingErrorListener.INSTANCE);

        return parser;
    }

    public static SMVExpr parseCellExpression(String cell, SVariable column, GeneralizedTestTable vars) {
        try {
            CellExpressionParser.CellContext p = createParser(cell).cell();
            ExprVisitor ev = new ExprVisitor(column, vars);
            SMVExpr expr = p.accept(ev);
            Report.debug("parsed: %s to %s", cell, expr);
            return expr;
        } catch (ParseCancellationException pce) {
            Report.error("Error in %s", cell);
            Report.error(pce.getMessage());
            throw pce;
        }
    }

    public static Duration parseDuration(String duration) {
        CellExpressionParser.Fixed_intervalContext p = createParser(duration).fixed_interval();
        Duration d = new Duration();
        if (p.c != null) {
            int i = Integer.parseInt(p.c.getText());
            d.lower = i;
            d.upper = i;
        } else if (p.MINUS() != null) {
            d.lower = 0;
            d.upper = -1;
        } else {
            d.lower = Integer.parseInt(p.a.getText());
            d.upper = Integer.parseInt(p.b.getText());
        }
        return d;
    }

    public static SVariable asSMVVariable(Variable column) {
        SVariable v = new SVariable(column.getName(),
                getSMVDataType(column.getDataType()));
        return v;
    }

    private static SMVType getSMVDataType(DataType dataType) {
        return DataTypeTranslator.INSTANCE.apply(dataType);
    }
}
