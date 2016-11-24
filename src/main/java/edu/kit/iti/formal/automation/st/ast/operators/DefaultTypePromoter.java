package edu.kit.iti.formal.automation.st.ast.operators;

import com.sun.org.apache.regexp.internal.RE;
import edu.kit.iti.formal.automation.datatypes.Any;

import java.util.ArrayList;
import java.util.LinkedList;

import static edu.kit.iti.formal.automation.datatypes.AnyInt.*;
import static edu.kit.iti.formal.automation.datatypes.AnyReal.LREAL;
import static edu.kit.iti.formal.automation.datatypes.AnyReal.REAL;

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
        return null;
    }
}
