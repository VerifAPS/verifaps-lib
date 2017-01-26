package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.expressions.BinaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.ExpressionVisitor;
import edu.kit.iti.formal.stvs.model.expressions.LiteralExpr;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.UnaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;

import java.util.Map;

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
  public ChocoExpressionWrapper visitBinaryFunction(BinaryFunctionExpr binaryFunctionExpr) {
    ChocoExpressionWrapper left = binaryFunctionExpr.getFirstArgument().takeVisitor(ChocoConvertExpressionVisitor.this);
    System.out.println(left);
    ChocoExpressionWrapper right = binaryFunctionExpr.getSecondArgument().takeVisitor(ChocoConvertExpressionVisitor.this);
    switch (binaryFunctionExpr.getOperation()) {
      case EQUALS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.eq(right.convertToArithmetic()))
        );
      case PLUS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.add(right.convertToArithmetic()))
        );
    }
    throw new IllegalArgumentException("Operation not implemented: " + binaryFunctionExpr.getOperation().name());
  }

  @Override
  public ChocoExpressionWrapper visitUnaryFunction(UnaryFunctionExpr unaryFunctionExpr) {
    ChocoExpressionWrapper argumentChoko = unaryFunctionExpr.getArgument().takeVisitor(this);
    switch (unaryFunctionExpr.getOperation()) {
      case NOT:
        return argumentChoko.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.getModel().intVar(1).sub(arExpression))
        );
    }
    throw new IllegalArgumentException("Operation not implemented: " + unaryFunctionExpr.getOperation().name());
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
    //If variable X is a backreference it will be indexed by X[-y]
    String variableName = variableExpr.getVariableName();
    String indexString = variableExpr.getIndex().map(index -> "[" + index + "]").orElse("");
    String fullName = variableName + indexString;
    //Check if variable is in typeContext
    if (!typeContext.containsKey(variableName)) {
      throw new IllegalStateException("Wrong Context: No variable of name '" + variableName + "' in typeContext");
    }
    Type type = typeContext.get(variableName);
    return type.match(
        () -> new ChocoExpressionWrapper(rowModel.addInt(fullName)),
        () -> new ChocoExpressionWrapper(rowModel.addBool(fullName)),
        (e) -> {
          //TODO: implement
          throw new IllegalStateException("Not implemented yet");
        }
    );
  }
}
