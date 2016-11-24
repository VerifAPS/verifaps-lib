package edu.kit.iti.formal.automation.datatypes.promotion;

import edu.kit.iti.formal.automation.datatypes.Any;

/**
 * Created by weigl on 24.11.16.
 */
public class SelfPromotion implements TypePromotion {
    public static final TypePromotion INSTANCE = new SelfPromotion();

    @Override
    public Any getPromotion(Any a, Any b) {
        if (a.equals(b))
            return a;
        else
            return null;
    }
}
