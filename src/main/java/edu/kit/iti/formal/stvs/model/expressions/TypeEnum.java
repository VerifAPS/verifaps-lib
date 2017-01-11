package edu.kit.iti.formal.stvs.model.expressions;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Supplier;

public class TypeEnum implements Type {

    private final String enumTypeName;
    private final Map<String, ValueEnum> valueMap;

    public TypeEnum(String enumTypeName, List<String> values) {
        this.enumTypeName = enumTypeName;
        this.valueMap = new HashMap<>();
        values.forEach((valueName) -> {
            valueMap.put(valueName, new ValueEnum(valueName, this));
        });
    }

    @Override
    public <R> R match(
            Supplier<R> matchIntType,
            Supplier<R> matchBoolType,
            Function<TypeEnum, R> matchEnumType) {
        return matchEnumType.apply(this);
    }

    @Override
    public boolean checksAgainst(Type other) {
        return other.match(
                () -> false,
                () -> false,
                (otherEnum) -> otherEnum.getTypeName().equals(getTypeName())
        );
    }

    @Override
    public String getTypeName() {
        return enumTypeName;
    }

    @Override
    public Value generateDefaultValue() {
        return null;
    }

    public ValueEnum valueOf(String enumName) {
        ValueEnum enumVal = valueMap.get(enumName);
        if (enumVal == null) {
            throw new RuntimeException("No enum value \"" + enumName + "\" for enum type: " + this);
        } else {
            return enumVal;
        }
    }

    public String toString() {
        return "TypeEnum(" + getTypeName() + ")";
    }

}
