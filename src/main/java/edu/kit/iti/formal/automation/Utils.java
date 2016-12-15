package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.values.Bits;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.exceptions.IllegalTypeException;
import edu.kit.iti.formal.automation.exceptions.OperatorNotFoundException;
import edu.kit.iti.formal.automation.operators.BinaryOperator;
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.automation.smv.DataTypeTranslator;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.ast.*;

/**
 * Created by weigl on 26.11.16.
 */
public class Utils {
    public static SBinaryOperator getSMVOperator(BinaryOperator operator) {
        switch (operator.symbol()) {
            case "+":
                return SBinaryOperator.PLUS;
            case "-":
                return SBinaryOperator.MINUS;
            case "*":
                return SBinaryOperator.MUL;
            case "/":
                return SBinaryOperator.DIV;
            case "MOD":
                return SBinaryOperator.MOD;
            case "AND":
                return SBinaryOperator.AND;
            case "OR":
                return SBinaryOperator.OR;
            case "<":
                return SBinaryOperator.LESS_THAN;
            case "<=":
                return SBinaryOperator.LESS_EQUAL;
            case ">":
                return SBinaryOperator.GREATER_THAN;
            case ">=":
                return SBinaryOperator.GREATER_EQUAL;
            case "=":
                return SBinaryOperator.EQUAL;
            case "<>":
                return SBinaryOperator.NOT_EQUAL;
        }
        throw new OperatorNotFoundException("Could not find: " + operator.symbol());
    }

    public static SUnaryOperator getSMVOperator(UnaryOperator operator) {
        switch (operator.symbol()) {
            case "NOT":
                return SUnaryOperator.NEGATE;
            case "-":
                return SUnaryOperator.MINUS;
        }
        throw new OperatorNotFoundException("Could not find " + operator.symbol());
    }

    public static SVariable asSMVVariable(VariableDeclaration name) {
        return new SVariable(name.getName(), Utils.getSMVDataType(name.getDataType()));
    }

    private static SMVType getSMVDataType(Any dataType) {
        DataTypeTranslator dtt = new DataTypeTranslator();
        return dataType.accept(dtt);
    }

    public static SLiteral asSMVLiteral(ScalarValue<? extends Any, ?> tsScalarValue) {
        if (tsScalarValue.getValue() instanceof Bits) {
            Bits value = (Bits) tsScalarValue.getValue();
            return asSMVLiteral(new ScalarValue<>(tsScalarValue.getDataType(), value.getRegister()));
        }
        return new SLiteral(getSMVDataType(tsScalarValue.getDataType()),
                tsScalarValue.getValue());
    }

    public static SMVExpr getDefaultValue(Any dataType) {
        if (dataType instanceof AnyInt) {
            return asSMVLiteral(new ScalarValue<>(dataType, 0));
        }

        if (dataType instanceof AnyBit.Bool) {
            return asSMVLiteral(ValueFactory.makeBool());
        }

        if (dataType instanceof AnyBit) {
            return asSMVLiteral(new ScalarValue<Any, Integer>(dataType, 0));
        }

        throw new IllegalTypeException();
    }

}
