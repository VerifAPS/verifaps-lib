package edu.kit.iti.formal.automation.datatypes.values;

import edu.kit.iti.formal.automation.datatypes.Any;

/**
 * Created by weigl on 10.06.14.
 */
public class RuntimeVariable {
    private String name;
    private Object value;
    private Any dataType;

    public RuntimeVariable(String name) {
        this.name = name;
    }

    public RuntimeVariable(String name, Any dataType) {
        this.name = name;
        this.dataType = dataType;
    }

    public RuntimeVariable(String name, Object value, Any dataType) {
        this.name = name;
        this.value = value;
        this.dataType = dataType;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public Object getValue() {
        return value;
    }

    public void setValue(Object value) {
        this.value = value;
    }

    public Any getDataType() {
        return dataType;
    }

    public void setDataType(Any dataType) {
        this.dataType = dataType;
    }
}
