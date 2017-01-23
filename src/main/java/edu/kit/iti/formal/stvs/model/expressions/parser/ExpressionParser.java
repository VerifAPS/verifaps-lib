package edu.kit.iti.formal.stvs.model.expressions.parser;

import edu.kit.iti.formal.stvs.model.expressions.*;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.*;

/**
 * Created by philipp on 09.01.17.
 */
public class ExpressionParser extends CellExpressionBaseVisitor<Expression> {

  private String columnName;
  private Expression columnAsVariable;
  private Map<String, ValueEnum> enumValues;

  public ExpressionParser(String columnName) {
    this.columnName = columnName;
    this.columnAsVariable = new VariableExpr(columnName);
    this.enumValues = new HashMap<>(); // empty enum value set, because no context given
  }

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
    try {
      return this.visit(parser.cell());
    } catch (ParseRuntimeException e) {
      throw e.getParseException();
    } catch (UnsupportedExpressionRuntimeException e) {
      throw e.getException();
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
        Arrays.asList(columnAsVariable, literalExpr));
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
    return new FunctionExpr(FunctionExpr.Operation.EQUALS,
        Arrays.asList(columnAsVariable, variableExpr));
  }

  @Override
  public Expression visitBvariable(CellExpressionParser.BvariableContext ctx) {
    return parseOccuringString(ctx.variable());
  }

  // A seemingly arbitrary string in a CellExpression can either be an Enum value or a variable...
  private Expression parseOccuringString(CellExpressionParser.VariableContext ctx) {
    return parseArrayIndex(ctx).map(index ->
        // If it has an index to it, like A[-2], its a variable for sure (indices don't make sense for enums!)
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
    FunctionExpr.Operation op = binaryOperationFromToken(ctx.op.relOp.getType());
    Expression rightSide = ctx.expr().accept(this);
    return new FunctionExpr(op,
        Arrays.asList(columnAsVariable, rightSide));
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
    return makeInterval(columnAsVariable, lower, upper);
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
