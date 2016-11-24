package edu.kit.iti.formal.automation.st.ast.operators;

import edu.kit.iti.formal.automation.datatypes.Any;

/**
 * Created by weigl on 24.11.16.
 */
public interface TypePromotion {
    Any getPromotion(Any a, Any b);
}
