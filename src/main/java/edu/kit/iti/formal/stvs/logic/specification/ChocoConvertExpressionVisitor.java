package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.ExpressionVisitor;
import edu.kit.iti.formal.stvs.model.expressions.FunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.LiteralExpr;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * This class provides a visitor for an Expression to convert it into a choco model
 */
public class ChocoConvertExpressionVisitor implements ExpressionVisitor<ChocoExpressionWrapper> {
  private ChocoModel rowModel = new ChocoModel("RowModel");
  private Map<String, Type> typeContext;


  /**
   * Creates a visitor from a type context.
   * The context is needed while visiting because of the logic in choco models
   *
   * @param typeContext A Map from variable names to types
   */
  public ChocoConvertExpressionVisitor(Map<String, Type> typeContext) {
    this.typeContext = typeContext;
  }


  /**
   * Returns the model which holds all constraints.
   *
   * @return the model
   */
  public ChocoModel getModel() {
    return rowModel;
  }

  @Override
  public ChocoExpressionWrapper visitFunctionExpr(FunctionExpr functionExpr) {
    List<Expression> arguments = functionExpr.getArguments();
    List<ChocoExpressionWrapper> chocoExpressions = arguments.stream()
        .map(expression -> expression.takeVisitor(this))
        .collect(Collectors.toList());
    switch (functionExpr.getOperation()) {
      case NOT:
        assureArgumentCount(chocoExpressions, 1);
        return chocoExpressions.get(0).autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.getModel().intVar(1).sub(arExpression))
        );
      case EQUALS:
        assureArgumentCount(chocoExpressions, 2);
        return chocoExpressions.get(0).autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.eq(chocoExpressions.get(1).convertToArithmetic()))
        );
      case PLUS:
        assureArgumentCount(chocoExpressions,2);
        return chocoExpressions.get(0).autoArithmetic(arExpression ->
          new ChocoExpressionWrapper(arExpression.add(chocoExpressions.get(1).convertToArithmetic()))
        );
    }
    throw new IllegalArgumentException("Operation not implemented: " + functionExpr.getOperation().name());
  }

  private static void assureArgumentCount(List<?> list, int expected) {
    if (list.size() != expected) {
      throw new IllegalStateException("Wrong number of arguments in FunctionExpr while converting to choco");
    }
  }


  @Override
  public ChocoExpressionWrapper visitLiteral(LiteralExpr literalExpr) {
    return literalExpr.getValue().match(
        (integ) -> new ChocoExpressionWrapper(rowModel.addIntLiteral(integ)),
        (bool) -> new ChocoExpressionWrapper(rowModel.addBoolLiteral(bool)),
        (e) -> null //TODO: implement
    );
  }

  @Override
  public ChocoExpressionWrapper visitVariable(VariableExpr variableExpr) {
    //Check if variable is a back reference
    if (variableExpr.getIndex().isPresent()) {
      //TODO: implement backreferences
    } else {
      String variableName = variableExpr.getVariableName();
      //Check if variable is in typeContext
      if (!typeContext.containsKey(variableName)) {
        throw new IllegalStateException("Wrong Context: No variable of name '" + variableName + "' in typeContext");
      }
      Type type = typeContext.get(variableName);
      return type.match(
          () -> new ChocoExpressionWrapper(rowModel.addInt(variableName)),
          () -> new ChocoExpressionWrapper(rowModel.addBool(variableName)),
          (e) -> null //TODO: implement
      );
    }
    return null;
  }
}
