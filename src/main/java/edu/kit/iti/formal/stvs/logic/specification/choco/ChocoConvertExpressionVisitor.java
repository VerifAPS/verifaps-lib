package edu.kit.iti.formal.stvs.logic.specification.choco;

import edu.kit.iti.formal.stvs.model.expressions.BinaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.ExpressionVisitor;
import edu.kit.iti.formal.stvs.model.expressions.LiteralExpr;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.UnaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.tools.VariableUtils;

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
    rowModel.init(typeContext);
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
      case AND:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.add(right.convertToArithmetic()).eq(2))
        );
      case OR:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.add(right.convertToArithmetic()).gt(0))
        );
      case XOR:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.add(right.convertToArithmetic()).eq(1))
        );
      case GREATER_THAN:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.gt(right.convertToArithmetic()))
        );
      case GREATER_EQUALS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.ge(right.convertToArithmetic()))
        );
      case LESS_THAN:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.lt(right.convertToArithmetic()))
        );
      case LESS_EQUALS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.le(right.convertToArithmetic()))
        );
      case EQUALS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.eq(right.convertToArithmetic()))
        );
      case NOT_EQUALS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.ne(right.convertToArithmetic()))
        );
      case PLUS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.add(right.convertToArithmetic()))
        );
      case MINUS:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.sub(right.convertToArithmetic()))
        );
      case MULTIPLICATION:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.mul(right.convertToArithmetic()))
        );
      case DIVISION:
        return left.autoArithmetic(arExpression -> {
              //return new ChocoExpressionWrapper(arExpression.div(right.convertToArithmetic()));
              /*
                Chocos domain bounds calculation is flawed.
                A new temporary variable for the result
                is introduced with the bounds defined in VariableUtils.boundsForDivision()
                if the right domain does not include elements of different signs.
                Otherwise [-A,A] with A=max(abs(leftLowerLimit),abs(leftUpperLimit))
               */
              IntVar rightAr = right.convertToArithmetic().intVar();
              IntVar leftAr = arExpression.intVar();
              int[] bounds;
              if (rightAr.contains(-1) && rightAr.contains(1)) {
                bounds = VariableUtils.boundsForDivision(leftAr, rightAr);
              }
              else{
                int maxDistanceToZero = Math.max(Math.abs(leftAr.getLB()), Math.abs(leftAr.getUB()));
                bounds = new int[]{-maxDistanceToZero, maxDistanceToZero};
              }
              IntVar result = arExpression.getModel().intVar(bounds[0], bounds[1]);
              Constraint constraint = arExpression.getModel().div(leftAr, right.convertToArithmetic().intVar(), result);
              constraint.post();
              return new ChocoExpressionWrapper(result);
            }
        );
      case MODULO:
        return left.autoArithmetic(arExpression -> {
              //new ChocoExpressionWrapper(arExpression.mod(right.convertToArithmetic()))
              /*
                Chocos domain bounds calculation is flawed.
                A new temporary variable for the result
                is introduced with the bounds [0, upperLimit of right expression]
                TODO: Check if ST allows negative results for modulo operations like Java(Script)
               */
              IntVar rightAr = right.convertToArithmetic().intVar();
              IntVar result = arExpression.getModel().intVar(0, rightAr.getUB());
              Constraint constraint = arExpression.getModel().mod(arExpression.intVar(), rightAr, result);
              constraint.post();
              return new ChocoExpressionWrapper(result);
            }
        );
      case POWER:
        return left.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.pow(right.convertToArithmetic()))
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
      case UNARY_MINUS:
        return argumentChoko.autoArithmetic(arExpression ->
            new ChocoExpressionWrapper(arExpression.neg())
        );
    }
    throw new IllegalArgumentException("Operation not implemented: " + unaryFunctionExpr.getOperation().name());
  }

  @Override
  public ChocoExpressionWrapper visitLiteral(LiteralExpr literalExpr) {
    return literalExpr.getValue().match(
        (integ) -> new ChocoExpressionWrapper(rowModel.addIntLiteral(integ)),
        (bool) -> new ChocoExpressionWrapper(rowModel.addBoolLiteral(bool)),
        (e) -> new ChocoExpressionWrapper(rowModel.addEnumLiteral(e.getType(), e.getEnumValue()))
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
        (e) -> new ChocoExpressionWrapper(rowModel.addEnum(fullName, e))
    );
  }
}
