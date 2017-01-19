package edu.kit.iti.formal.stvs.model.expressions.parser;

import edu.kit.iti.formal.stvs.model.expressions.*;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.Arrays;
import java.util.Optional;

/**
 * Created by philipp on 09.01.17.
 */
public class ExpressionParser extends CellExpressionBaseVisitor<Expression> {

  private String cellName;
  private Expression cellAsVariable;

  public ExpressionParser(String cellName) {
    this.cellName = cellName;
    this.cellAsVariable = new VariableExpr(cellName);
  }

  /**
   * @param expressionAsString the String to interpret as cell-expression
   * @return the expression covering the semantics of the given string interpreted as cell-expression.
   * @throws ParseException                 When parsing could not be successful
   * @throws UnsupportedExpressionException When unsupported grammar features are reached
   */
  public Expression parseExpression(String expressionAsString) throws ParseException, UnsupportedExpressionException {
    CharStream charStream = new ANTLRInputStream(expressionAsString);
    CellExpressionLexer lexer = new CellExpressionLexer(charStream);
    TokenStream tokens = new CommonTokenStream(lexer);
    CellExpressionParser parser = new CellExpressionParser(tokens);
    parser.removeErrorListeners();
    parser.addErrorListener(new ThrowingErrorListener());
    try {
      return this.visit(parser.cell());
    } catch (ParseRuntimeException e) {
      throw e.getParseException();
    } catch (UnsupportedExpressionRuntimeException e) {
      throw e.getException();
    }
  }

  public String getCellName() {
    return cellName;
  }

  public void setCellName(String cellName) {
    this.cellName = cellName;
  }

  @Override
  public Expression visit(ParseTree tree) {
    return tree.accept(this);
  }

  @Override
  public Expression visitCell(CellExpressionParser.CellContext ctx) {
    Optional<Expression> optionalExpression = ctx.chunk().stream()
        .map(chunkContext -> chunkContext.accept(this))
        .reduce((e1, e2) ->
            new FunctionExpr(FunctionExpr.Operation.AND, Arrays.asList(e1, e2)));
    return optionalExpression.get();
  }

  @Override
  public Expression visitDontcare(CellExpressionParser.DontcareContext ctx) {
    return new LiteralExpr(ValueBool.TRUE);
  }

  @Override
  public Expression visitConstant(CellExpressionParser.ConstantContext ctx) {
    Expression literalExpr = new LiteralExpr(valueFromConstantToken(ctx));
    return new FunctionExpr(FunctionExpr.Operation.EQUALS,
        Arrays.asList(cellAsVariable, literalExpr));
  }

  @Override
  public Expression visitBconstant(CellExpressionParser.BconstantContext ctx) {
    return new LiteralExpr(valueFromConstantToken(ctx.constant()));
  }

  @Override
  public Expression visitVariable(CellExpressionParser.VariableContext ctx) {
    Expression variableExpr = new VariableExpr(ctx.getText());
    return new FunctionExpr(FunctionExpr.Operation.EQUALS,
        Arrays.asList(cellAsVariable, variableExpr));
  }

  @Override
  public Expression visitBvariable(CellExpressionParser.BvariableContext ctx) {
    return new VariableExpr(ctx.getText());
  }

  private Value valueFromConstantToken(CellExpressionParser.ConstantContext ctx) {
    // I have to trust ANTLR to not have any other values here... :/
    switch (ctx.a.getType()) {
      case CellExpressionLexer.INTEGER:
        return new ValueInt(Integer.parseInt(ctx.getText()));
      case CellExpressionLexer.T:
        return ValueBool.TRUE;
      case CellExpressionLexer.F:
        return ValueBool.FALSE;
      default:
        return null;
    }
  }

  @Override
  public Expression visitSinglesided(CellExpressionParser.SinglesidedContext ctx) {
    FunctionExpr.Operation op = binaryOperationFromToken(ctx.op.relOp.getType());
    Expression rightSide = ctx.expr().accept(this);
    return new FunctionExpr(op,
        Arrays.asList(cellAsVariable, rightSide));
  }

  private FunctionExpr.Operation binaryOperationFromToken(int token) {
    switch (token) {
      case CellExpressionLexer.EQUALS:
        return FunctionExpr.Operation.EQUALS;
      case CellExpressionLexer.NOT_EQUALS:
        return FunctionExpr.Operation.NOT_EQUALS;
      case CellExpressionLexer.GREATER_THAN:
        return FunctionExpr.Operation.GREATER_THAN;
      case CellExpressionLexer.GREATER_EQUALS:
        return FunctionExpr.Operation.GREATER_EQUALS;
      case CellExpressionLexer.LESS_THAN:
        return FunctionExpr.Operation.LESS_THAN;
      case CellExpressionLexer.LESS_EQUALS:
        return FunctionExpr.Operation.LESS_EQUALS;
      case CellExpressionLexer.NOT:
        return FunctionExpr.Operation.NOT;
      case CellExpressionLexer.AND:
        return FunctionExpr.Operation.AND;
      case CellExpressionLexer.OR:
        return FunctionExpr.Operation.OR;
      case CellExpressionLexer.XOR:
        return FunctionExpr.Operation.XOR;
      case CellExpressionLexer.PLUS:
        return FunctionExpr.Operation.PLUS;
      case CellExpressionLexer.MINUS:
        return FunctionExpr.Operation.MINUS;
      case CellExpressionLexer.MULT:
        return FunctionExpr.Operation.MULTIPLICATION;
      case CellExpressionLexer.DIV:
        return FunctionExpr.Operation.DIVISION;
      case CellExpressionLexer.MOD:
        return FunctionExpr.Operation.MODULO;
      default:
        return null;
    }
  }

  @Override
  public Expression visitPlus(CellExpressionParser.PlusContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.PLUS,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitSubstract(CellExpressionParser.SubstractContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.MINUS,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitMult(CellExpressionParser.MultContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.MULTIPLICATION,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitDiv(CellExpressionParser.DivContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.DIVISION,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitMod(CellExpressionParser.ModContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.MODULO,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitLogicalAnd(CellExpressionParser.LogicalAndContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.AND,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitLogicalXor(CellExpressionParser.LogicalXorContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.XOR,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitLogicalOr(CellExpressionParser.LogicalOrContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.OR,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitInequality(CellExpressionParser.InequalityContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.NOT_EQUALS,
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitEquality(CellExpressionParser.EqualityContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.EQUALS,
        Arrays.asList(left, right));
  }


  @Override
  public Expression visitCompare(CellExpressionParser.CompareContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new FunctionExpr(binaryOperationFromToken(ctx.op.getType()),
        Arrays.asList(left, right));
  }

  @Override
  public Expression visitInterval(CellExpressionParser.IntervalContext ctx) {
    Expression lower = ctx.lower.accept(this);
    Expression upper = ctx.upper.accept(this);
    return makeInterval(cellAsVariable, lower, upper);
  }

  // Transforms: variable "X", lower "-5", upper "1+2" into "x >= -5 && x <= 1+2" as expression
  private Expression makeInterval(Expression variable, Expression lower, Expression upper) {
    Expression greaterThanLower = new FunctionExpr(
        FunctionExpr.Operation.GREATER_EQUALS, Arrays.asList(variable, lower));
    Expression smallerThanUpper = new FunctionExpr(
        FunctionExpr.Operation.LESS_EQUALS, Arrays.asList(variable, upper));

    return new FunctionExpr(FunctionExpr.Operation.AND,
        Arrays.asList(greaterThanLower, smallerThanUpper));
  }

  @Override
  public Expression visitMinus(CellExpressionParser.MinusContext ctx) {
    Expression toBeNegated = ctx.sub.accept(this);
    return new FunctionExpr(FunctionExpr.Operation.UNARY_MINUS, Arrays.asList(toBeNegated));
  }

  @Override
  public Expression visitNegation(CellExpressionParser.NegationContext ctx) {
    return new FunctionExpr(FunctionExpr.Operation.NOT, Arrays.asList(ctx.sub.accept(this)));
  }

  @Override
  public Expression visitParens(CellExpressionParser.ParensContext ctx) {
    return ctx.sub.accept(this);
  }

  @Override
  public Expression visitGuardedcommand(CellExpressionParser.GuardedcommandContext ctx) {
    throw new UnsupportedExpressionRuntimeException("Guarded command (if)");
  }

  @Override
  public Expression visitFunctioncall(CellExpressionParser.FunctioncallContext ctx) {
    throw new UnsupportedExpressionRuntimeException("Functioncall");
  }

}
