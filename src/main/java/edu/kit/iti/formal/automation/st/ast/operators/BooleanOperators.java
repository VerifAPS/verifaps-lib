package edu.kit.iti.formal.automation.st.ast.operators;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyBit;

/**
 * Created by weigl on 24.11.16.
 */
public class BooleanOperators extends BinaryOperator {

    public BooleanOperators(String symbol) {
        super(symbol, AnyBit.BOOL);
        promoter = BooleanPromoter.INSTANCE;
    }
}
