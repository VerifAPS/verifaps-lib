package edu.kit.iti.formal.stvs.model.expressions.parser;

import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import org.antlr.v4.runtime.*;

import java.util.Optional;

/**
 * A class for parsing fixed interval expressions like <tt>[1,-]</tt> or <tt>[1,5]</tt>,
 * defined by the ANTLR grammar in antlr/CellExpression.g4.
 * This parser does not need any context information and does not capture state
 * and thus is a singleton.
 */
public class IntervalParser extends CellExpressionBaseVisitor<LowerBoundedInterval> {

  private static final IntervalParser INSTANCE = new IntervalParser();

  /**
   * Parse an interval, for example <tt>[1,-]</tt> or <tt>-</tt> (a wildcard)
   * or <tt>[1,4]</tt>. Only fixed values are allowed, no variables.
   * @param intervalAsString the string to be parsed.
   * @return a LowerBoundedInterval as the runtime representation of interval strings.
   * @throws ParseException in case the string doesn't fit the given fixed-interval grammar.
   */
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
    } catch (ParseRuntimeException runtimeException) {
      throw runtimeException.getParseException();
    }
  }

  @Override
  public LowerBoundedInterval visitFixed_interval(CellExpressionParser.Fixed_intervalContext ctx) {
    // If the Interval is a simple interval like [1,3] or [5,-]
    if (ctx.a != null && ctx.b != null) {
      int lowerBound = parsePositive(ctx.a);
      String upperBoundString = ctx.b.getText();

      if ("-".equals(upperBoundString)) {
        return new LowerBoundedInterval(lowerBound, Optional.empty());
      } else {
        int upperBoundInt = parsePositive(ctx.b);
        if (upperBoundInt < lowerBound) {
          throw new ParseRuntimeException(
              new ParseException(ctx.b.getLine(), ctx.b.getCharPositionInLine(),
                  "Upper bound is lower than lower bound"));
        }
        return new LowerBoundedInterval(lowerBound, Optional.of(upperBoundInt));
      }
    // if the interval string is just a constant, like "6" -> [6,6]
    } else if (ctx.c != null) {
      int value = parsePositive(ctx.c);
      return new LowerBoundedInterval(value, Optional.of(value));
    }
    // Only case left is the wildcard "-"
    return new LowerBoundedInterval(0, Optional.empty());
  }

  private int parsePositive(Token token) {
    int number = Integer.parseInt(token.getText());
    if (number < 0) {
      throw new ParseRuntimeException(
          new ParseException(token.getLine(), token.getCharPositionInLine(),
              "Interval boundary must be positive."));
    }
    return number;
  }

}
