package edu.kit.iti.formal.automation.datatypes.promotion;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.AnyReal;

/**
 * Created by weigl on 24.11.16.
 */
public class RealPromotion implements TypePromotion {

    public static final TypePromotion INSTANCE = new RealPromotion();

    @Override
    public Any getPromotion(Any a, Any b) {
        try {
            return promote((AnyReal) a, (AnyReal) b);
        } catch (ClassCastException e) {
            try {
                return promote((AnyReal) a, (AnyInt) b);
            } catch (ClassCastException e1) {
                try {
                    return promote((AnyReal) b, (AnyInt) a);
                } catch (ClassCastException e2) {
                    return null;
                }
            }
        }
    }

    private Any promote(AnyReal a, AnyInt b) {
        return a;
    }

    private Any promote(AnyReal a, AnyReal b) {
        if (a.equals(b)) return a;
        if (a instanceof AnyReal.LReal) {
            return a;
        } else {
            return b;
        }
    }
}