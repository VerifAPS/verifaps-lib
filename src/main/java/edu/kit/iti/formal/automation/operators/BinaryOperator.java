package edu.kit.iti.formal.automation.operators;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.promotion.DefaultTypePromoter;
import edu.kit.iti.formal.automation.datatypes.promotion.TypePromotion;

/**
 * Created by weigl on 24.11.16.
 */
public class BinaryOperator implements Operator {
    final String symbol;
    final Any validType;
    protected TypePromotion promoter = new DefaultTypePromoter();

    protected BinaryOperator(String symbol, Any validType) {
        this.symbol = symbol;
        this.validType = validType;
        Operators.register(symbol, this);
    }

    public boolean isTypeConform(Any argument) {
        return argument.getClass().isAssignableFrom(validType.getClass());
    }

    @Override
    public String symbol() {
        return symbol;
    }

    @Override
    public Any[] getExpectedDataTypes() {
        return new Any[]{validType, validType};
    }

    public Any getPromotedType(Any left, Any right) {
        return promoter.getPromotion(left, right);
    }

}