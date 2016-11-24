package edu.kit.iti.formal.automation.st.ast.operators;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.AnySignedInt;
import edu.kit.iti.formal.automation.datatypes.AnyUInt;

/**
 * Created by weigl on 24.11.16.
 */
public class IntegerPromotion implements TypePromotion {
    public static final IntegerPromotion INSTANCE = new IntegerPromotion();

    @Override
    public Any getPromotion(Any a, Any b) {
        try {
            return promote((AnySignedInt) a, (AnySignedInt) b);
        } catch (ClassCastException e) {
            try {
                return promote((AnyUInt) a, (AnyUInt) b);
            } catch (ClassCastException e1) {
                try {
                    return promote((AnySignedInt) a, (AnyUInt) b);
                } catch (ClassCastException e2) {
                    return promote((AnySignedInt) b, (AnyUInt) a);
                }
            }
        }
    }

    public Any promote(AnySignedInt a, AnySignedInt b) {
        if (a.getBitLength() >= b.getBitLength())
            return a;
        else
            return b;
    }


    public Any promote(AnyUInt a, AnyUInt b) {
        if (a.getBitLength() >= b.getBitLength())
            return a;
        else
            return b;
    }

    public Any promote(AnySignedInt a, AnyUInt b) {
        if (a.getBitLength() > b.getBitLength())
            return a;
        else
            return b.asSigned();
    }
}
