package edu.kit.iti.formal.automation.datatypes;

import java.util.Arrays;

/**
 * Created by weigl on 10.06.14.
 */
public class EnumerateType extends Any {
    private String name;
    private String[] allowedValues;
    private String defValue;
    private int bitlength;

    public EnumerateType() {
        //the unknown type
    }

    public EnumerateType(String name, String[] allowedValues) {
        this(name, allowedValues, allowedValues[0]);
    }

    public EnumerateType(String name, String[] allowedValues, String defValue) {
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

    public String[] getAllowedValues() {
        return allowedValues;
    }

    public void setAllowedValues(String[] allowedValues) {
        this.allowedValues = allowedValues;
        Arrays.sort(this.allowedValues);
        bitlength = (int) Math.ceil(Math.log(allowedValues.length));
    }

    public String getDefValue() {
        return defValue;
    }

    public void setDefValue(String defValue) {
        assert Arrays.binarySearch(allowedValues, defValue) != -1;
        this.defValue = defValue;
    }

    @Override
    public String repr(Object obj) {
        if (name == null) return String.valueOf(obj);
        else return name + "#" + obj;
    }
}
