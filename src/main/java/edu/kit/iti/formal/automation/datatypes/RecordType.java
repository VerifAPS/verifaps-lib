package edu.kit.iti.formal.automation.datatypes;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 10.06.14.
 */
public class RecordType extends Any {
    private String name;
    private List<Field> fields = new ArrayList<>();

    public RecordType(String name) {
        this.name = name;
    }

    public List<Field> getFields() {
        return fields;
    }

    public void addField(String name, Any dataType) {
        fields.add(new Field(name, dataType));
    }

    @Override
    public String repr(Object obj) {
        return null;
    }


    public class Field {
        private String name;
        private Any dataType;
        private Object defValue;

        public Field(String name, Any dataType) {
            this.name = name;
            this.dataType = dataType;
        }

        public String getName() {
            return name;
        }

        public void setName(String name) {
            this.name = name;
        }

        public Any getDataType() {
            return dataType;
        }

        public void setDataType(Any dataType) {
            this.dataType = dataType;
        }

        public Object getDefValue() {
            return defValue;
        }

        public void setDefValue(Object defValue) {
            this.defValue = defValue;
        }

    }


    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
