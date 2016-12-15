package edu.kit.iti.formal.automation.datatypes.promotion;

import edu.kit.iti.formal.automation.datatypes.Any;

import java.util.ArrayList;

/**
 * Type Promotion based on a table.
 * Created by weigl on 24.11.16.
 */
public class DefaultTypePromoter implements TypePromotion {
    ArrayList<TypePromotion> promoters = new ArrayList<>();

    public DefaultTypePromoter() {
        promoters.add(IntegerPromotion.INSTANCE);
        promoters.add(BitPromotion.INSTANCE);
        promoters.add(RealPromotion.INSTANCE);
        promoters.add(SelfPromotion.INSTANCE);
    }

    @Override
    public Any getPromotion(Any a, Any b) {
        for (TypePromotion tp : promoters) {
            Any c = tp.getPromotion(a, b);
            if (c != null) return c;
        }
        return null;
    }
}
