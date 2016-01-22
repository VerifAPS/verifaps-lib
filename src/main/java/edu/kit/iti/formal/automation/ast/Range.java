package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;

/**
 * Created by weigl on 13.06.14.
 */
public class Range {
    private ScalarValue<? extends AnyInt, Long> start;
    private ScalarValue<? extends AnyInt, Long> stop;

    public Range(ScalarValue<? extends AnyInt, Long> start, ScalarValue<? extends AnyInt, Long> stop) {
        this.start = start;
        this.stop = stop;
    }

    public ScalarValue<? extends AnyInt, Long> getStart() {
        return start;
    }

    public void setStart(ScalarValue<? extends AnyInt, Long> start) {
        this.start = start;
    }

    public ScalarValue<? extends AnyInt, Long> getStop() {
        return stop
                ;
    }

    public void setStop(ScalarValue<? extends AnyInt, Long> stop) {
        this.stop = stop;
    }
}
