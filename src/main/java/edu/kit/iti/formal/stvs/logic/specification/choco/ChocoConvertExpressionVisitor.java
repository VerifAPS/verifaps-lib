package edu.kit.iti.formal.stvs.logic.specification.choco;

import edu.kit.iti.formal.stvs.model.expressions.BinaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.ExpressionVisitor;
import edu.kit.iti.formal.stvs.model.expressions.LiteralExpr;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.UnaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;
import org.chocosolver.solver.constraints.extension.TuplesFactory;
import org.chocosolver.solver.expression.discrete.arithmetic.ArExpression;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.tools.MathUtils;
import org.chocosolver.util.tools.VariableUtils;

import java.util.Arrays;
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
    ChocoExpressionWrapper right = binaryFunctionExpr.getSecondArgument().takeVisitor(ChocoConvertExpressionVisitor.this);
    ArExpression leftAr = left.convertToArithmetic();
    ArExpression rightAr = right.convertToArithmetic();
    IntVar result;
    switch (binaryFunctionExpr.getOperation()) {
      case AND:
        return new ChocoExpressionWrapper(leftAr.add(rightAr).eq(2));
      case OR:
        return new ChocoExpressionWrapper(leftAr.add(rightAr).gt(0));
      case XOR:
        return new ChocoExpressionWrapper(leftAr.add(rightAr).eq(1));
      case GREATER_THAN:
        return new ChocoExpressionWrapper(leftAr.gt(rightAr));
      case GREATER_EQUALS:
        return new ChocoExpressionWrapper(leftAr.ge(rightAr));
      case LESS_THAN:
        return new ChocoExpressionWrapper(leftAr.lt(rightAr));
      case LESS_EQUALS:
        return new ChocoExpressionWrapper(leftAr.le(rightAr));
      case EQUALS:
        return new ChocoExpressionWrapper(leftAr.eq(rightAr));
      case NOT_EQUALS:
        return new ChocoExpressionWrapper(leftAr.ne(rightAr));
      case PLUS:
        int[] boundsForAddition = VariableUtils.boundsForAddition(leftAr.intVar(), rightAr.intVar());
        boundsForAddition = preventOverflowBounds(boundsForAddition);
        result = leftAr.getModel().intVar(boundsForAddition[0], boundsForAddition[1]);
        leftAr.getModel().arithm(leftAr.intVar(), "+", rightAr.intVar(), "=", result).post();
        return new ChocoExpressionWrapper(result);
      case MINUS:
        int[] boundsForSubtraction = VariableUtils.boundsForSubstraction(leftAr.intVar(), rightAr.intVar());
        boundsForSubtraction = preventOverflowBounds(boundsForSubtraction);
        result = leftAr.getModel().intVar(boundsForSubtraction[0], boundsForSubtraction[1]);
        leftAr.getModel().arithm(leftAr.intVar(), "-", rightAr.intVar(), "=", result).post();
        return new ChocoExpressionWrapper(result);
      case MULTIPLICATION:
        int[] boundsForMultiplication = VariableUtils.boundsForMultiplication(leftAr.intVar(), rightAr.intVar());
        boundsForMultiplication = preventOverflowBounds(boundsForMultiplication);
        result = leftAr.getModel().intVar(boundsForMultiplication[0], boundsForMultiplication[1]);
        leftAr.getModel().times(leftAr.intVar(), rightAr.intVar(), result).post();
        return new ChocoExpressionWrapper(result);
      case DIVISION:
        //return new ChocoExpressionWrapper(arExpression.div(right.convertToArithmetic()));
        /*
          Chocos domain bounds calculation is flawed.
          A new temporary variable for the result
          is introduced with the bounds defined in VariableUtils.boundsForDivision()
          if the right domain does not include elements of different signs.
          Otherwise [-A,A] with A=max(abs(leftLowerLimit),abs(leftUpperLimit))
         */
        int[] bounds;
        if (rightAr.intVar().contains(-1) && rightAr.intVar().contains(1)) {
          bounds = VariableUtils.boundsForDivision(leftAr.intVar(), rightAr.intVar());
        } else {
          int maxDistanceToZero = Math.max(Math.abs(leftAr.intVar().getLB()), Math.abs(leftAr.intVar().getUB()));
          bounds = new int[]{-maxDistanceToZero, maxDistanceToZero};
        }
        result = leftAr.getModel().intVar(bounds[0], bounds[1]);
        leftAr.getModel().div(leftAr.intVar(), rightAr.intVar(), result).post();
        return new ChocoExpressionWrapper(result);
      case MODULO:
        //new ChocoExpressionWrapper(arExpression.mod(right.convertToArithmetic()))
        /*
          Chocos domain bounds calculation is flawed.
          A new temporary variable for the result
          is introduced with the bounds [0, upperLimit of right expression]
          TODO: Check if ST allows negative results for modulo operations like Java(Script)
         */
        result = leftAr.getModel().intVar(0, rightAr.intVar().getUB());
        leftAr.getModel().mod(leftAr.intVar(), rightAr.intVar(), result).post();
        return new ChocoExpressionWrapper(result);
      //TODO: Test
      case POWER:
        int[] boundsForPower = VariableUtils.boundsForPow(leftAr.intVar(), rightAr.intVar());
        boundsForPower = preventOverflowBounds(boundsForPower);
        result = leftAr.getModel().intVar(boundsForPower[0], boundsForPower[1]);

        //The following 3 lines are copied from BiArArxpression (Choco) und untested
        leftAr.getModel().table(new IntVar[]{rightAr.intVar(), leftAr.intVar(), result},
            TuplesFactory.generateTuples(vs -> vs[2] == MathUtils.pow(vs[0], vs[1]),
                true, rightAr.intVar(), leftAr.intVar(), result)).post();
        return new ChocoExpressionWrapper(result);
    }
    throw new

        IllegalArgumentException("Operation not implemented: " + binaryFunctionExpr.getOperation().

        name());
  }

  private int[] preventOverflowBounds(int[] bounds) {
    return Arrays.stream(bounds)
        .map(bound -> Math.min(bound, ChocoModel.MAX_BOUND))
        .map(bound -> Math.max(bound, ChocoModel.MIN_BOUND))
        .toArray();
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
