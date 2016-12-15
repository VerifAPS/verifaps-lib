package edu.kit.iti.formal.automation.datatypes.promotion;

import edu.kit.iti.formal.automation.datatypes.Any;

/**
 * Created by weigl on 24.11.16.
 */
public class EnumPromoter implements TypePromotion {

    @Override
    public Any getPromotion(Any a, Any b) {
        /*public Any conformTo (Any dataType){
            if (dataType instanceof AnyInt) {
                AnyInt type = (AnyInt) dataType;
                if (type.bitLength < bitlength) {
                    return AnyInt.INT.conformTo(type);
                } else {
                    return type;
                }
            }*/
        return null;
    }
}
