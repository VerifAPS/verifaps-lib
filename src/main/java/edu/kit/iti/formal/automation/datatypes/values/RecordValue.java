package edu.kit.iti.formal.automation.datatypes.values;

import edu.kit.iti.formal.automation.datatypes.RecordType;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 10.06.14.
 */
public class RecordValue {
    private RecordType recordType;
    private Map<String, RuntimeVariable> fieldValues = new HashMap<>();

    public RecordValue(RecordType recordType) {
        this.recordType = recordType;

        for (RecordType.Field field : recordType.getFields()) {
            fieldValues.put(field.getName(),
                    new RuntimeVariable(field.getName(), field.getDefValue(), field.getDataType())
            );
        }
    }

    public Map<String, RuntimeVariable> getFieldValues() {
        return fieldValues;
    }

    public void setFieldValues(Map<String, RuntimeVariable> fieldValues) {
        this.fieldValues = fieldValues;
    }
}
