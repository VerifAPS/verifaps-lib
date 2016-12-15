package edu.kit.iti.formal.smv.ast;

public enum GroundDataType {
    SIGNED_WORD(true),
    UNSIGNED_WORD(true),
    INT, FLOAT, BOOLEAN, ENUM;

    public boolean hasWidth;

    GroundDataType() {
        this(false);
    }

    GroundDataType(boolean has_width) {
        hasWidth = has_width;
    }

    public Object parse(String value) {
        switch (this) {
            case FLOAT:
                return Float.parseFloat(value);
            case ENUM:
                return value;
            case INT:
            case SIGNED_WORD:
            case UNSIGNED_WORD:
                return Integer.parseInt(value);
            case BOOLEAN:
                return Boolean.parseBoolean(value);
        }
        return value;
    }

    public String format(Object value) {
        if (this == BOOLEAN) {
            boolean b = false;
            if (value instanceof Boolean) {
                b = (Boolean) value;
            }

            if (value instanceof Integer)
                b = ((Integer) value) != 0;

            if (value instanceof Long)
                b = ((Long) value) != 0;

            return Boolean.toString(b).toUpperCase();
        }
        return "" + value;
    }

}
