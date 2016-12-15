package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;

/**
 * Created by weigl on 13.06.14.
 */
public class StringTypeDeclaration extends TypeDeclaration<ScalarValue<? extends IECString, String>> {
    private ScalarValue<? extends AnyInt, Long> size;

    public ScalarValue<? extends IECString, String> getInitializationValue() {
        return initializationValue;
    }

    public void setInitializationValue(ScalarValue<? extends IECString, String> initializationValue) {
        this.initializationValue = initializationValue;

    }

    public ScalarValue<? extends AnyInt, Long> getSize() {
        return size;
    }

    public void setSize(ScalarValue<? extends AnyInt, Long> size) {
        this.size = size;
    }

    @Override
    public Any getDataType(GlobalScope globalScope) {
        //TODO
        setBaseType(IECString.STRING_16BIT);
        return getBaseType();
    }

    @Override
    public <S> S visit(Visitor<S> visitor) {
        return visitor.visit(this);
    }
}
