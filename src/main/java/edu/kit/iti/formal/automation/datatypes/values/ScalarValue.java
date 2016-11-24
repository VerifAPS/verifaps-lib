package edu.kit.iti.formal.automation.datatypes.values;

import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.Initialization;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.ast.VariableScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 */
public class ScalarValue<T extends Any, S> extends Expression implements Value<T>, Initialization {
    private T dataType;
    private S value;


    public ScalarValue(T dataType, S value) {
        this.dataType = dataType;
        this.value = value;
    }

    @Override
    public T getDataType() {
        return dataType;
    }

    public void setDataType(T dataType) {
        this.dataType = dataType;
    }

    public S getValue() {
        return value;
    }

    public void setValue(S value) {
        this.value = value;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "ScalarValue{" +
                "dataType=" + dataType +
                ", value=" + value +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ScalarValue)) return false;

        ScalarValue that = (ScalarValue) o;

        if (dataType != null ? !dataType.equals(that.dataType) : that.dataType != null) return false;
        if (value != null ? !value.equals(that.value) : that.value != null) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = dataType != null ? dataType.hashCode() : 0;
        result = 31 * result + (value != null ? value.hashCode() : 0);
        return result;
    }

    @Override
    public Any dataType(VariableScope scope) {
        return getDataType();
    }
}
