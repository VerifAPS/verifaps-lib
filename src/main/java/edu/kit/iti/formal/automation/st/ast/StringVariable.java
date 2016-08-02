package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;

/**
 * Created by weigl on 13.06.14.
 */
public class StringVariable extends VariableDeclaration {
    private ScalarValue<? extends AnyInt, Long> length;

    public StringVariable(String name, Integer peek, ScalarValue<? extends AnyInt, Long> length, ScalarValue<? extends IECString, String> def) {
        super(name, peek);
        this.length = length;
        setInit(def);
    }

    public ScalarValue<? extends AnyInt, Long> getLength() {
        return length;
    }

    public void setLength(ScalarValue<? extends AnyInt, Long> length) {
        this.length = length;
    }
}
