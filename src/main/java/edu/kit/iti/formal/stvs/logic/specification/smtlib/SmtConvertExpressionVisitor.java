package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.automation.datatypes.Int;
import edu.kit.iti.formal.stvs.logic.specification.choco.ChocoExpressionWrapper;
import edu.kit.iti.formal.stvs.logic.specification.choco.ChocoModel;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.*;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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
  private final List<SExpr> globalConstraints;
  private final Integer row;
  private final SpecIoVariable column;
  private final Predicate<Type> isIoVariable;


  /**
   * Creates a visitor from a type context.
   * The context is needed while visiting because of the logic in choco models
   *
   * @param typeContext A Map from variable names to types
   * @param row row, that the visitor should convert
   */
  public SmtConvertExpressionVisitor(Map<String, Type> typeContext, Integer row, SpecIoVariable
      column, Predicate<Type> isIoVariable) {
    this.typeContext = typeContext;
    this.globalConstraints = createEnumTypes();
    this.row = row;
    this.isIoVariable = isIoVariable;
    this.column = column;
  }

  private List<SExpr> createEnumTypes() {
    typeContext.entrySet().stream().map(item -> {
      String typeName = item.getValue().getTypeName();
      List<ValueEnum> valueEnums = item.getValue().match(
          LinkedList::new,
          LinkedList::new,
          TypeEnum::getValues
      );
      List<String> arguments = valueEnums.stream().map(ValueEnum::getValueString).collect(Collectors.toList());
      /*
      (declare-datatypes () ((Color red green blue)))
       */
      return new SList("declare-datatypes", new SList(), new SList(
          (new SList(typeName)).addListElements(arguments)
      ));
    }).collect(Collectors.toList());
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
    Integer variableReference = variableExpr.getIndex().orElse(0);

    //Check if variable is in typeContext
    if (!typeContext.containsKey(variableName)) {
      throw new IllegalStateException("Wrong Context: No variable of name '" + variableName + "' in typeContext");
    }
    Type type = typeContext.get(variableName);

    if(isIoVariable.test(type)) {
      // Do Rule IV
      
      // Do Rule II
    } else {
      return new SAtom(variableName);
    }
  }
}
