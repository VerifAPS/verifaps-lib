package edu.kit.iti.formal.stvs.model.expressions.parser;

import edu.kit.iti.formal.stvs.model.code.SyntaxErrorListener;
import edu.kit.iti.formal.stvs.model.expressions.*;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * This class parses Expressions using the ANTLR parser generator library.
 * The resulting Expression format is an {@link Expression}.
 */
public class ExpressionParser extends CellExpressionBaseVisitor<Expression> {

  private String columnName;
  private Expression columnAsVariable;
  private Map<String, ValueEnum> enumValues;

  /**
   * Creates an Expression parser without a type context.
   * That means this parser can't parse enums.
   * @param columnName name of this column's IoVariable for
   *                   parsing single-sided expressions.
   */
  public ExpressionParser(String columnName) {
    this.columnName = columnName;
    this.columnAsVariable = new VariableExpr(columnName);
    this.enumValues = new HashMap<>(); // empty enum value set, because no context given
  }

  /**
   * @param columnName name of this column's IoVariable for
   *                   parsing single-sided expressions.
   * @param typeContext available types for figuring out whether
   *                    an occuring string in an expression is
   *                    an enum-literal.
   */
  public ExpressionParser(String columnName, Set<Type> typeContext) {
    this.columnName = columnName;
    this.columnAsVariable = new VariableExpr(columnName);
    this.enumValues = computeEnumValuesByName(typeContext);
  }

  private Map<String, ValueEnum> computeEnumValuesByName(Set<Type> typeSet) {
    Map<String, ValueEnum> byName = new HashMap<>();
    typeSet.stream()
        .map(this::filterEnumType)
        .filter(Optional::isPresent)
        .map(Optional::get) // Filter only the TypeEnums out of there
        .forEach(typeEnum ->
          typeEnum.getValues().forEach(valueEnum -> // For every possible enum value
            byName.put(valueEnum.getEnumValue(), valueEnum) // sort it in by name
          ));
    return byName;
  }

  private Optional<TypeEnum> filterEnumType(Type type) {
    return type.match(
        Optional::empty, // If its a TypeInt
        Optional::empty, // If its a TypeBool
        Optional::of     // If its a TypeEnum
    );
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
    parser.addErrorListener(new SyntaxErrorListener());
    try {
      return this.visit(parser.cell());
    } catch (ParseRuntimeException runtimeException) {
      throw runtimeException.getParseException();
    } catch (UnsupportedExpressionRuntimeException runtimeException) {
      throw runtimeException.getException();
    }
  }

  public String getColumnName() {
    return columnName;
  }

  public void setColumnName(String columnName) {
    this.columnName = columnName;
    this.columnAsVariable = new VariableExpr(columnName);
  }

  public void setTypeContext(Set<Type> context) {
    this.enumValues = computeEnumValuesByName(context);
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
            new BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, e1, e2));
    // We can always .get() this value, since the grammar enforces
    // that at least one chunk exists in a cell.
    return optionalExpression.get();
  }

  @Override
  public Expression visitDontcare(CellExpressionParser.DontcareContext ctx) {
    return new LiteralExpr(ValueBool.TRUE);
  }

  @Override
  public Expression visitConstant(CellExpressionParser.ConstantContext ctx) {
    Expression literalExpr = new LiteralExpr(valueFromConstantToken(ctx));
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, columnAsVariable, literalExpr);
  }

  @Override
  public Expression visitBconstant(CellExpressionParser.BconstantContext ctx) {
    return new LiteralExpr(valueFromConstantToken(ctx.constant()));
  }

  @Override
  public Expression visitVariable(CellExpressionParser.VariableContext ctx) {
    // If we come here, its a top-level variable.
    // In this case there's an implicit equality with the column variable.
    Expression variableExpr = parseOccuringString(ctx);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, columnAsVariable, variableExpr);
  }

  @Override
  public Expression visitBvariable(CellExpressionParser.BvariableContext ctx) {
    return parseOccuringString(ctx.variable());
  }

  // A seemingly arbitrary string in a CellExpression can either be an Enum value or a variable...
  private Expression parseOccuringString(CellExpressionParser.VariableContext ctx) {
    return parseArrayIndex(ctx).map(index ->
        // If it has an index to it, like A[-2], its a variable for sure
        // (indices don't make sense for enums!)
        (Expression) new VariableExpr(parseIdentifier(ctx), index)) // really java? really?
        // Otherwise we still have to find out
        .orElse(maybeParseEnum(ctx));
  }

  private Expression maybeParseEnum(CellExpressionParser.VariableContext ctx) {
    String identifier = parseIdentifier(ctx);
    ValueEnum enumValue = enumValues.get(identifier);

    // If the enum value exists, we take it, else we think it's a variable.
    if (enumValue == null) {
      return new VariableExpr(identifier);
    } else {
      return new LiteralExpr(enumValue);
    }
  }

  private Optional<Integer> parseArrayIndex(CellExpressionParser.VariableContext ctx) {
    return Optional.ofNullable(ctx.INTEGER())
        .map(node -> {
          int index = Integer.valueOf(node.getText());
          if (index > 0) {
            throw new UnsupportedExpressionRuntimeException("Positive Variable Index");
          }
          return index;
        });
  }

  private String parseIdentifier(CellExpressionParser.VariableContext ctx) {
    return ctx.IDENTIFIER().getText();
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
    BinaryFunctionExpr.Op op = binaryOperationFromToken(ctx.op.relOp);
    Expression rightSide = ctx.expr().accept(this);
    return new BinaryFunctionExpr(op, columnAsVariable, rightSide);
  }

  private BinaryFunctionExpr.Op binaryOperationFromToken(Token token) {
    switch (token.getType()) {
      case CellExpressionLexer.EQUALS:
        return BinaryFunctionExpr.Op.EQUALS;
      case CellExpressionLexer.NOT_EQUALS:
        return BinaryFunctionExpr.Op.NOT_EQUALS;
      case CellExpressionLexer.GREATER_THAN:
        return BinaryFunctionExpr.Op.GREATER_THAN;
      case CellExpressionLexer.GREATER_EQUALS:
        return BinaryFunctionExpr.Op.GREATER_EQUALS;
      case CellExpressionLexer.LESS_THAN:
        return BinaryFunctionExpr.Op.LESS_THAN;
      case CellExpressionLexer.LESS_EQUALS:
        return BinaryFunctionExpr.Op.LESS_EQUALS;
      case CellExpressionLexer.AND:
        return BinaryFunctionExpr.Op.AND;
      case CellExpressionLexer.OR:
        return BinaryFunctionExpr.Op.OR;
      case CellExpressionLexer.XOR:
        return BinaryFunctionExpr.Op.XOR;
      case CellExpressionLexer.PLUS:
        return BinaryFunctionExpr.Op.PLUS;
      case CellExpressionLexer.MINUS:
        return BinaryFunctionExpr.Op.MINUS;
      case CellExpressionLexer.MULT:
        return BinaryFunctionExpr.Op.MULTIPLICATION;
      case CellExpressionLexer.DIV:
        return BinaryFunctionExpr.Op.DIVISION;
      case CellExpressionLexer.MOD:
        return BinaryFunctionExpr.Op.MODULO;
      default:
        throw new ParseRuntimeException(
            new ParseException(token.getLine(), token.getCharPositionInLine(),
                "Unsupported singlesided operation: \"" + token.getType() + "\"")
        );
    }
  }

  @Override
  public Expression visitPlus(CellExpressionParser.PlusContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, left, right);
  }

  @Override
  public Expression visitSubstract(CellExpressionParser.SubstractContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.MINUS, left, right);
  }

  @Override
  public Expression visitMult(CellExpressionParser.MultContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.MULTIPLICATION, left, right);
  }

  @Override
  public Expression visitDiv(CellExpressionParser.DivContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.DIVISION, left, right);
  }

  @Override
  public Expression visitMod(CellExpressionParser.ModContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.MODULO, left, right);
  }

  @Override
  public Expression visitLogicalAnd(CellExpressionParser.LogicalAndContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, left, right);
  }

  @Override
  public Expression visitLogicalXor(CellExpressionParser.LogicalXorContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.XOR, left, right);
  }

  @Override
  public Expression visitLogicalOr(CellExpressionParser.LogicalOrContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.OR, left, right);
  }

  @Override
  public Expression visitInequality(CellExpressionParser.InequalityContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.NOT_EQUALS, left, right);
  }

  @Override
  public Expression visitEquality(CellExpressionParser.EqualityContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, left, right);
  }


  @Override
  public Expression visitCompare(CellExpressionParser.CompareContext ctx) {
    Expression left = ctx.left.accept(this);
    Expression right = ctx.right.accept(this);
    return new BinaryFunctionExpr(binaryOperationFromToken(ctx.op), left, right);
  }

  @Override
  public Expression visitInterval(CellExpressionParser.IntervalContext ctx) {
    Expression lower = ctx.lower.accept(this);
    Expression upper = ctx.upper.accept(this);
    return makeInterval(columnAsVariable, lower, upper);
  }

  // Transforms: variable "X", lower "-5", upper "1+2" into "x >= -5 && x <= 1+2" as expression
  private Expression makeInterval(Expression variable, Expression lower, Expression upper) {
    Expression greaterThanLower = new BinaryFunctionExpr(
        BinaryFunctionExpr.Op.GREATER_EQUALS, variable, lower);
    Expression smallerThanUpper = new BinaryFunctionExpr(
        BinaryFunctionExpr.Op.LESS_EQUALS, variable, upper);

    return new BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, greaterThanLower, smallerThanUpper);
  }

  @Override
  public Expression visitMinus(CellExpressionParser.MinusContext ctx) {
    Expression toBeNegated = ctx.sub.accept(this);
    return new UnaryFunctionExpr(UnaryFunctionExpr.Op.UNARY_MINUS, toBeNegated);
  }

  @Override
  public Expression visitNegation(CellExpressionParser.NegationContext ctx) {
    return new UnaryFunctionExpr(UnaryFunctionExpr.Op.NOT, ctx.sub.accept(this));
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
