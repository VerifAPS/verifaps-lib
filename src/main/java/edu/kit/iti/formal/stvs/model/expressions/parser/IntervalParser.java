package edu.kit.iti.formal.stvs.model.expressions.parser;

import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.TokenStream;

import java.util.Optional;

/**
 * Created by philipp on 23.01.17.
 */
public class IntervalParser extends CellExpressionBaseVisitor<LowerBoundedInterval> {

  private static final IntervalParser INSTANCE = new IntervalParser();

  public static LowerBoundedInterval parse(String intervalAsString) throws ParseException {
    CharStream charStream = new ANTLRInputStream(intervalAsString);
    CellExpressionLexer lexer = new CellExpressionLexer(charStream);
    TokenStream tokens = new CommonTokenStream(lexer);
    CellExpressionParser parser = new CellExpressionParser(tokens);
    parser.removeErrorListeners();
    parser.addErrorListener(new ThrowingErrorListener());
    try {
      CellExpressionParser.Fixed_intervalContext ctx = parser.fixed_interval();
      if (ctx == null) {
        throw new ParseException(0, 0, "Expected fixed interval");
      }
      return INSTANCE.visit(ctx);
    } catch (ParseRuntimeException e) {
      throw e.getParseException();
    }
  }

  @Override
  public LowerBoundedInterval visitFixed_interval(CellExpressionParser.Fixed_intervalContext ctx) {
    // If the Interval is a simple interval like [1,3] or [5,-]
    if (ctx.a != null && ctx.b != null) {
      int lowerBound = Integer.valueOf(ctx.a.getText());
      String upperBoundString = ctx.b.getText();

      if ("-".equals(upperBoundString)) {
        return new LowerBoundedInterval(lowerBound, Optional.empty());
      } else {
        int upperBoundInt = Integer.valueOf(upperBoundString);
        if (upperBoundInt < lowerBound) {
          throw new ParseRuntimeException(
              new ParseException(ctx.b.getLine(), ctx.b.getStartIndex(), "Upper bound is lower than lower bound"));
        }
        return new LowerBoundedInterval(lowerBound, Optional.of(upperBoundInt));
      }
    // if the interval string is just a constant, like "6" -> [6,6]
    } else if (ctx.c != null) {
      int value = Integer.valueOf(ctx.c.getText());
      return new LowerBoundedInterval(value, Optional.of(value));
    }
    // Only case left is the wildcard "-"
    return new LowerBoundedInterval(0, Optional.empty());
  }

}
