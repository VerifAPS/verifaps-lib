package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;
import edu.kit.iti.formal.automation.datatypes.AnyInt;

/**
 * Created by weigl on 13.06.14.
 */
public class SubRangeDataType extends TypeDeclaration<ScalarValue<? extends AnyInt, Long>> {
    private Range range;

    public Range getRange() {
        return range;
    }

    public void setRange(Range range) {
        this.range = range;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
