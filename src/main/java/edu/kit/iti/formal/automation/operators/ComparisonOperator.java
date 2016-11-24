package edu.kit.iti.formal.automation.operators;

import edu.kit.iti.formal.automation.datatypes.AnyNum;

/**
 * Created by weigl on 24.11.16.
 */
public class ComparisonOperator extends BinaryOperator {
    ComparisonOperator(String symbol) {
        super(symbol, new AnyNum());
        promoter = new BooleanPromoter();
    }


}
