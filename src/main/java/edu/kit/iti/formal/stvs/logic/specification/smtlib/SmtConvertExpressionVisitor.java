package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.*;

import java.util.HashMap;
import java.util.Map;

/**
 * This class provides a visitor for an expression to convert it into a smt model.
 *
 * @author Carsten Csiky
 */
public class SmtConvertExpressionVisitor implements ExpressionVisitor<SExpression> {
  //static maps

  private static Map<UnaryFunctionExpr.Op, String> smtlibUnaryOperationNames =
      new HashMap<UnaryFunctionExpr.Op, String>() {
        {
          put(UnaryFunctionExpr.Op.NOT, "not");
          put(UnaryFunctionExpr.Op.UNARY_MINUS, "bvneg");
        }
      };
  private static Map<BinaryFunctionExpr.Op, String> smtlibBinOperationNames =
      new HashMap<BinaryFunctionExpr
          .Op, String>() {
        {
          put(BinaryFunctionExpr.Op.AND, "and");
          put(BinaryFunctionExpr.Op.OR, "or");
          put(BinaryFunctionExpr.Op.XOR, "xor");
          put(BinaryFunctionExpr.Op.DIVISION, "bvsdiv");
          put(BinaryFunctionExpr.Op.MULTIPLICATION, "bvmul");
          put(BinaryFunctionExpr.Op.EQUALS, "=");
          put(BinaryFunctionExpr.Op.GREATER_EQUALS, "bvsge");
          put(BinaryFunctionExpr.Op.LESS_EQUALS, "bvsle");
          put(BinaryFunctionExpr.Op.LESS_THAN, "bvslt");
          put(BinaryFunctionExpr.Op.GREATER_THAN, "bvsgt");
          put(BinaryFunctionExpr.Op.MINUS, "bvsub");
          put(BinaryFunctionExpr.Op.PLUS, "bvadd");
          put(BinaryFunctionExpr.Op.MODULO, "bvsmod");
        }
      };

  private final SmtEncoder smtEncoder;
  private final int row;
  private final int iteration;
  private final ValidIoVariable column;

  private final SmtModel constraint;

  /**
   * Creates a visitor to convert an expression to a set of constraints.
   *
   * @param smtEncoder encoder that holds additional information
   *                   about the expression that should be parsed
   * @param row        row, that holds the cell the visitor should convert
   * @param iteration  current iteration
   * @param column     column, that holds the cell the visitor should convert
   */
  public SmtConvertExpressionVisitor(SmtEncoder smtEncoder, int row, int
      iteration, ValidIoVariable column) {
    this.smtEncoder = smtEncoder;
    this.row = row;
    this.iteration = iteration;
    this.column = column;

    String name = "|" + column.getName() + "_" + row + "_" + iteration + "|";

    this.constraint = new SmtModel().addHeaderDefinitions(
        new SList(
            "declare-const",
            name,
            SmtEncoder.getSmtLibVariableTypeName(column.getValidType())
        )
    );

    //Constrain enum bitvectors to their valid range
    column.getValidType().match(
        () -> null,
        () -> null,
        enumeration -> {
          addEnumBitvectorConstraints(name, enumeration);
          return null;
        }
    );
  }

  /**
   * Adds constraints to enum variables to limit the range of their representing bitvector.
   *
   * @param name        Name of solver variable
   * @param enumeration Type of enumeration
   */
  private void addEnumBitvectorConstraints(String name, TypeEnum enumeration) {
    this.constraint.addGlobalConstrains(
        new SList("bvsge", name, BitvectorUtils.hexFromInt(0, 4)));
    this.constraint.addGlobalConstrains(
        new SList("bvslt", name, BitvectorUtils.hexFromInt(enumeration.getValues().size(), 4)));
  }


  @Override
  public SExpression visitBinaryFunction(BinaryFunctionExpr binaryFunctionExpr) {
    SExpression left = binaryFunctionExpr.getFirstArgument().takeVisitor(SmtConvertExpressionVisitor
        .this);
    SExpression right = binaryFunctionExpr.getSecondArgument().takeVisitor(
        SmtConvertExpressionVisitor.this);

    switch (binaryFunctionExpr.getOperation()) {
      case NOT_EQUALS:
        return new SList("not", new SList("=", left, right));
      default:
        String name = smtlibBinOperationNames.get(binaryFunctionExpr.getOperation());
        if (name == null) {
          throw new IllegalArgumentException("Operation "
              + binaryFunctionExpr.getOperation() + " is "
              + "not supported");
        }
        return new SList(name, left, right);
    }
  }

  @Override
  public SExpression visitUnaryFunction(UnaryFunctionExpr unaryFunctionExpr) {
    SExpression argument = unaryFunctionExpr.getArgument().takeVisitor(this);
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
  public SExpression visitLiteral(LiteralExpr literalExpr) {
    String literalAsString = literalExpr.getValue().match(
        integer -> BitvectorUtils.hexFromInt(integer, 4),
        bool -> bool ? "true" : "false",
        this::getEnumValueAsBitvector
    );
    return new SAtom(literalAsString);
  }

  private String getEnumValueAsBitvector(ValueEnum enumeration) {
    return BitvectorUtils.hexFromInt(enumeration.getType().getValues().indexOf(enumeration), 4);
  }

  /*private String integerLiteralAsBitVector(int integer, int length){

  }*/

  @Override
  public SExpression visitVariable(VariableExpr variableExpr) {
    String variableName = variableExpr.getVariableName();
    Integer variableReferenceIndex = variableExpr.getIndex().orElse(0);

    //Check if variable is in getTypeForVariable
    if (smtEncoder.getTypeForVariable(variableName) == null) {
      throw new IllegalStateException(
          "Wrong Context: No variable of name '" + variableName + "' in getTypeForVariable");
    }
    Type type = smtEncoder.getTypeForVariable(variableName);

    // is an IOVariable?
    if (smtEncoder.isIoVariable(variableName)) {
      // Do Rule (3)

      //does it reference a previous cycle? -> guarantee reference-ability
      if (variableReferenceIndex < 0) {
        constraint.addGlobalConstrains(
            // sum(z-1) >= max(0, alpha - i)
            new SList(
                "bvuge",
                sumRowIterations(row - 1),
                new SAtom(BitvectorUtils.hexFromInt(
                    Math.max(0, -(iteration + variableReferenceIndex)), 4))
            )
        );
      }

      // Do Rule part of Rule (I)
      // A[-v] -> A_z_(i-v)
      return new SAtom("|" + variableName + "_" + row + "_" + (iteration
          + variableReferenceIndex) + "|");

      //return new SAtom(variableName);
    } else {
      return new SAtom("|" + variableName + "|");
    }
  }

  private SExpression sumRowIterations(int j) {
    SList list = new SList().addAll("bvadd");

    for (int l = 0; l <= j; l++) {
      list.addAll("n_" + l);
    }
    return list;
  }

  public SmtModel getConstraint() {
    return constraint;
  }
}
