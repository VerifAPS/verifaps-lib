package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.BinaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.ExpressionVisitor;
import edu.kit.iti.formal.stvs.model.expressions.LiteralExpr;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.UnaryFunctionExpr;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * This class provides a visitor for an Expression to convert it into a choco model
 */
public class SmtConvertExpressionVisitor implements ExpressionVisitor<SExpr> {
  //static maps

  private static Map<UnaryFunctionExpr.Op, String> smtlibUnaryOperationNames = new HashMap<UnaryFunctionExpr.Op, String>() {{
    put(UnaryFunctionExpr.Op.NOT, "not");
    put(UnaryFunctionExpr.Op.UNARY_MINUS, "bvneg");
  }};
  private static Map<BinaryFunctionExpr.Op, String> smtlibBinOperationNames = new HashMap<BinaryFunctionExpr
      .Op, String>() {{
    put(BinaryFunctionExpr.Op.AND, "and");
    put(BinaryFunctionExpr.Op.OR, "or");
    put(BinaryFunctionExpr.Op.XOR, "xor");
    put(BinaryFunctionExpr.Op.DIVISION, "bvsrem");
    put(BinaryFunctionExpr.Op.MULTIPLICATION, "bvmul");
    put(BinaryFunctionExpr.Op.EQUALS, "=");
    put(BinaryFunctionExpr.Op.GREATER_EQUALS, "bvsge");
    put(BinaryFunctionExpr.Op.LESS_EQUALS, "bvsle");
    put(BinaryFunctionExpr.Op.LESS_THAN, "bvslt");
    put(BinaryFunctionExpr.Op.GREATER_THAN, "bvsgt");
    put(BinaryFunctionExpr.Op.MINUS, "bvsub");
    put(BinaryFunctionExpr.Op.PLUS, "bvadd");
    put(BinaryFunctionExpr.Op.MODULO, "bvsrem");
  }};

  private final Function<String, Type> getTypeForVariable;
  private final int row;
  private final int iteration;
  private final ValidIoVariable column;
  private final Predicate<String> isIoVariable;
  private final Function<Type, String> getSMTLibVariableName;

  private final SConstraint sConstraint;

  /**
   * Creates a visitor from a type context.
   * The context is needed while visiting because of the logic in choco models
   *
   * @param getTypeForVariable        A Map from variable names to types
   * @param row                       row, that the visitor should convert
   * @param getSMTLibVariableTypeName
   */
  public SmtConvertExpressionVisitor(Function<String, Type> getTypeForVariable, int row, int
      iteration, ValidIoVariable column, Predicate<String> isIoVariable, Function<Type, String>
                                         getSMTLibVariableTypeName) {
    this.getTypeForVariable = getTypeForVariable;
    this.row = row;
    this.iteration = iteration;
    this.isIoVariable = isIoVariable;
    this.column = column;
    this.getSMTLibVariableName = getSMTLibVariableTypeName;

    String name = "|" + column.getName() + "_" + row + "_" + iteration + "|";

    this.sConstraint = new SConstraint().addHeaderDefinitions(
        new SList(
            "declare-const",
            name,
            getSMTLibVariableTypeName.apply(column.getValidType())
        )
    );

    //Constrain enum bitvectors to their valid range
    column.getValidType().match(
        () -> null,
        () -> null,
        enumeration -> {
          this.sConstraint.addGlobalConstrains(new SList("bvsge", name, BitvectorUtils.hexFromInt(0, 4)));
          this.sConstraint.addGlobalConstrains(new SList("bvslt", name, BitvectorUtils.hexFromInt(enumeration.getValues().size(), 4)));
          return null;
        }
    );
  }


  @Override
  public SExpr visitBinaryFunction(BinaryFunctionExpr binaryFunctionExpr) {
    SExpr left = binaryFunctionExpr.getFirstArgument().takeVisitor(SmtConvertExpressionVisitor
        .this);
    SExpr right = binaryFunctionExpr.getSecondArgument().takeVisitor
        (SmtConvertExpressionVisitor.this);

    switch (binaryFunctionExpr.getOperation()) {
      case NOT_EQUALS:
        return new SList("not", new SList("=", left, right));
      default:
        String name = smtlibBinOperationNames.get(binaryFunctionExpr.getOperation());
        if (name == null) {
          throw new IllegalArgumentException("Operation " + binaryFunctionExpr.getOperation() + " is "
              + "not supported");
        }
        return new SList(name, left, right);
    }
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
    String literalAsString = literalExpr.getValue().match(
        integer -> BitvectorUtils.hexFromInt(integer, 4),
        bool -> bool ? "true" : "false",
        enumeration -> BitvectorUtils.hexFromInt(enumeration.getType().getValues().indexOf(enumeration), 4)
    );
    return new SAtom(literalAsString);
  }

  /*private String integerLiteralAsBitVector(int integer, int length){

  }*/

  @Override
  public SExpr visitVariable(VariableExpr variableExpr) {
    String variableName = variableExpr.getVariableName();
    Integer variableReferenceIndex = variableExpr.getIndex().orElse(0);

    //Check if variable is in getTypeForVariable
    if (getTypeForVariable.apply(variableName) == null) {
      throw new IllegalStateException("Wrong Context: No variable of name '" + variableName + "' in getTypeForVariable");
    }
    Type type = getTypeForVariable.apply(variableName);

    // is an IOVariable?
    if (isIoVariable.test(variableName)) {
      // Do Rule I

      //does it reference a previous cycle? -> guarantee reference-ability
      if (variableReferenceIndex < 0) {
        sConstraint.addGlobalConstrains(
            // sum(z-1) >= max(0, alpha - i)
            new SList(
                "bvuge",
                sumRowIterations(row - 1),
                new SAtom(BitvectorUtils.hexFromInt(Math.max(0, -(iteration + variableReferenceIndex)),4))
            )
        );
      }

      // Do Rule II
      // A[-v] -> A_z_(i-v)
      return new SAtom("|" + variableName + "_" + row + "_" + (iteration +
          variableReferenceIndex) + "|");

      //return new SAtom(variableName);
    } else {
      return new SAtom("|" + variableName + "|");
    }
  }

  private SExpr sumRowIterations(int j) {
    SList list = new SList().addAll("bvadd");

    for (int l = 0; l <= j; l++) {
      list.addAll("n_" + l);
    }
    return list;
  }

  public SConstraint getConstraint() {
    return sConstraint;
  }
}
