package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.specification.choco.ChocoModel;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.*;

import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * This class provides a visitor for an Expression to convert it into a choco model
 */
public class SmtConvertExpressionVisitor implements ExpressionVisitor<SExpr> {
  //static maps

  private static Map<UnaryFunctionExpr.Op, String> smtlibUnaryOperationNames = new HashMap<UnaryFunctionExpr.Op, String>() {{
    put(UnaryFunctionExpr.Op.NOT, "not");
  }};
  private static Map<BinaryFunctionExpr.Op, String> smtlibBinOperationNames = new HashMap<BinaryFunctionExpr
      .Op, String>() {{
    put(BinaryFunctionExpr.Op.AND, "and");
    put(BinaryFunctionExpr.Op.OR, "or");
    put(BinaryFunctionExpr.Op.DIVISION, "/");
    put(BinaryFunctionExpr.Op.MULTIPLICATION, "*");
    put(BinaryFunctionExpr.Op.EQUALS, "=");
    put(BinaryFunctionExpr.Op.GREATER_EQUALS, ">=");
    put(BinaryFunctionExpr.Op.LESS_EQUALS, "<=");
    put(BinaryFunctionExpr.Op.LESS_THAN, "<");
    put(BinaryFunctionExpr.Op.GREATER_THAN, ">");
    put(BinaryFunctionExpr.Op.MINUS, "-");
    put(BinaryFunctionExpr.Op.PLUS, "+");
  }};

  private final Map<String, Type> typeContext;
  private final int row;
  private final int iteration;
  private final SpecIoVariable column;
  private final Predicate<Type> isIoVariable;
  private final Function<String, String> getSMTLibVariableName;

  private final SConstraint sConstraint;

  /**
   * Creates a visitor from a type context.
   * The context is needed while visiting because of the logic in choco models
   *  @param typeContext A Map from variable names to types
   * @param row row, that the visitor should convert
   * @param getSMTLibVariableTypeName
   */
  public SmtConvertExpressionVisitor(Map<String, Type> typeContext, int row, int
      iteration, SpecIoVariable column, Predicate<Type> isIoVariable, Function<String, String> getSMTLibVariableTypeName) {
    this.typeContext = typeContext;
    this.row = row;
    this.iteration = iteration;
    this.isIoVariable = isIoVariable;
    this.column = column;
    this.getSMTLibVariableName = getSMTLibVariableTypeName;

    String typeName = column.getType().getTypeName();
    this.sConstraint = new SConstraint().addHeaderDefinitions(
        new SList(
            "declare-const",
            column.getName() + "_" + row + "_" + iteration,
            /*try to get type-name for smtlibTypes -> in case of an enum use our naming
            *(b/c we define it that way in SmtPreprocessor)
            * */
            getSMTLibVariableTypeName.apply(typeName)
        )
    );
  }


  @Override
  public SExpr visitBinaryFunction(BinaryFunctionExpr binaryFunctionExpr) {
    SExpr left = binaryFunctionExpr.getFirstArgument().takeVisitor(SmtConvertExpressionVisitor
        .this);
    SExpr right = binaryFunctionExpr.getSecondArgument().takeVisitor
        (SmtConvertExpressionVisitor.this);
    String name = smtlibBinOperationNames.get(binaryFunctionExpr.getOperation());
    if (name == null) {
      throw new IllegalArgumentException("Operation " + binaryFunctionExpr.getOperation() + " is "
          + "not supported");
    }
    return new SList(name, left, right);

  }



  private int[] preventOverflowBounds(int[] bounds) {
    return Arrays.stream(bounds)
        .map(bound -> Math.min(bound, ChocoModel.MAX_BOUND))
        .map(bound -> Math.max(bound, ChocoModel.MIN_BOUND))
        .toArray();
  }

  @Override
  public SExpr visitUnaryFunction(UnaryFunctionExpr unaryFunctionExpr) {
    SExpr argument = unaryFunctionExpr.getArgument().takeVisitor(this);
    String name = smtlibUnaryOperationNames.get(unaryFunctionExpr.getOperation());

    if (name == null) {
      if (unaryFunctionExpr.getOperation() == UnaryFunctionExpr.Op.UNARY_MINUS) {
        return new SList("-", new SAtom("0"), argument);
      } else {
        throw new IllegalArgumentException("Operation " + unaryFunctionExpr.getOperation() + "is "
            + "not supported");
      }
    }
    return new SList(name, argument);
  }

  @Override
  public SExpr visitLiteral(LiteralExpr literalExpr) {
    return new SAtom(literalExpr.getValue().getValueString());
  }

  @Override
  public SExpr visitVariable(VariableExpr variableExpr) {
    String variableName = variableExpr.getVariableName();
    Integer variableReferenceIndex = variableExpr.getIndex().orElse(0);

    //Check if variable is in typeContext
    if (!typeContext.containsKey(variableName)) {
      throw new IllegalStateException("Wrong Context: No variable of name '" + variableName + "' in typeContext");
    }
    Type type = typeContext.get(variableName);

    // is an IOVariable?
    if (isIoVariable.test(type)) {
      // Do Rule I
      // sum_(i=0...(z-1))(n_i) >= j
      sConstraint.addGlobalConstrains(
          new SList(
              ">=",
              sumRowIterations(row - 1),
              new SAtom((iteration - variableReferenceIndex) + "")
          )
      );
      // Do Rule II
      // A[-v] -> A_z_(i-v)
      return new SAtom(variableName + "_" + row + "_" + (iteration - variableReferenceIndex));

      //return new SAtom(variableName);
    } else {
      return new SAtom(variableName);
    }
  }

  private SExpr sumRowIterations(int j) {
    SList list = new SList().addAll("+");

    for (int l = 0; l <= j; l++) {
      list.addAll("n_"+l);
    }
    return list;
  }

  public SConstraint getConstraint() {
    return sConstraint;
  }
}
