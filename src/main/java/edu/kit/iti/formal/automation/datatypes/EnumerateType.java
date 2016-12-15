package edu.kit.iti.formal.automation.datatypes;

import java.util.List;

/**
 * Created by weigl on 10.06.14.
 */
public class EnumerateType extends Any {
    private String name;
    private List<String> allowedValues;
    private String defValue;
    private int bitlength;

    public EnumerateType() {
        //the unknown type
    }

    public EnumerateType(String name, List<String> allowedValues) {
        this(name, allowedValues, allowedValues.get(0));
    }

    public EnumerateType(String name, List<String> allowedValues, String defValue) {
        this.name = name;
        setAllowedValues(allowedValues);
        setDefValue(defValue);
    }

    public EnumerateType(String prefix) {
        this.name = prefix;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public List<String> getAllowedValues() {
        return allowedValues;
    }

    public void setAllowedValues(List<String> allowedValues) {
        this.allowedValues = allowedValues;
        bitlength = (int) Math.ceil(Math.log(allowedValues.size()));
    }

    public String getDefValue() {
        return defValue;
    }

    public void setDefValue(String defValue) {
        assert allowedValues.contains(defValue);
        this.defValue = defValue;
    }

    @Override
    public String repr(Object obj) {
        if (name == null) return String.valueOf(obj);
        else return name + "#" + obj;
    }


    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
