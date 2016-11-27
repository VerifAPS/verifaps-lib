package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.exceptions.IllegalTypeException;
import edu.kit.iti.formal.automation.exceptions.OperatorNotFoundException;
import edu.kit.iti.formal.automation.operators.BinaryOperator;
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.ast.*;

/**
 * Created by weigl on 26.11.16.
 */
public class Utils {
    public static SBinaryOperator getSMVOperator(BinaryOperator operator) {
        for (SBinaryOperator o : SBinaryOperator.values()) {
            if (o.symbol().equals(operator.symbol()))
                return o;
        }
        throw new OperatorNotFoundException();
    }

    public static SUnaryOperator getSMVOperator(UnaryOperator operator) {
        for (SUnaryOperator o : SUnaryOperator.values()) {
            if (o.name().equals(operator.symbol()))
                return o;
        }
        throw new OperatorNotFoundException();
    }

    public static SVariable asSMVVariable(VariableDeclaration name) {
        return new SVariable(name.getName(), Utils.getSMVDataType(name.getDataType()));
    }

    private static SMVType getSMVDataType(Any dataType) {
        if (dataType instanceof AnyInt) {
            AnyInt inttype = (AnyInt) dataType;
            return new SMVType.SMVTypeWithWidth(
                    inttype.isSigned() ?
                            GroundDataType.SIGNED_WORD :
                            GroundDataType.UNSIGNED_WORD, inttype.getBitLength());
        }
        if (dataType instanceof AnyBit.Bool) {
            return SMVType.BOOLEAN;
        }
        if (dataType instanceof AnyBit) {
            return new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD,
                    ((AnyBit) dataType).getBitLength());
        }
        throw new IllegalTypeException();
    }

    public static SLiteral asSMVLiteral(ScalarValue<? extends Any, ?> tsScalarValue) {
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
