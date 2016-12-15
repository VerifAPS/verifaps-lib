package edu.kit.iti.formal.smv.ast;

import java.util.List;

public class SMVType {
    public static final SMVType BOOLEAN = new SMVType(GroundDataType.BOOLEAN);

    public GroundDataType base;

    public SMVType() {
    }

    public SMVType(GroundDataType b) {
        base = b;
    }

    public static SMVType infer(List<SMVType> list) {
        //TODO
        return null;
    }

    public static SMVType infer(SMVType a, SMVType b) {
        //TODO
        return null;
    }

    public static class SMVTypeWithWidth extends SMVType {
        int width;

        public SMVTypeWithWidth(GroundDataType dt, int i) {
            super(dt);
            width = i;
        }

        public int getWidth() {
            return width;
        }

        @Override
        public String toString() {
            return String.format("%s word[%d]",
                    (base == GroundDataType.UNSIGNED_WORD
                            ? "unsigned" : "signed")
                    , width);
        }

        @Override
        public String format(Object value) {
            long l = 0;
            if (value instanceof String) {
                l = Long.parseLong(value.toString());
            } else if (value instanceof Integer) {
                Integer integer = (Integer) value;
                l = integer;
            } else if (value instanceof Long) {
                l = (Long) value;
            }

            return String.format("%s0%sd%d_%d",
                    (l < 0 ? "-" : ""),
                    (base == GroundDataType.SIGNED_WORD ? "s" : "u"),
                    width,
                    Math.abs(l));
        }
    }

    public static class EnumType extends SMVType {
        List<String> values;

        public EnumType(List<String> id) {
            values = id;
        }

        public SLiteral valueOf(String value) {
            SLiteral l = super.valueOf(value);
            if (!values.contains(l.value)) {
                throw new IllegalArgumentException();
            }
            return l;
        }

        @Override
        public String format(Object value) {
            return value.toString();
        }

        @Override
        public String toString() {
            return "{" + values.stream().reduce((a, b) -> a + ", " + b).get() + "}";
        }
    }

    public static SMVType unsigned(int i) {
        return new SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, i);
    }

    public static SMVType signed(int i) {
        return new SMVTypeWithWidth(GroundDataType.SIGNED_WORD, i);
    }

    public SLiteral valueOf(String value) {
        SLiteral l = new SLiteral();
        l.dataType = this;
        l.value = base.parse(value);
        return l;
    }

    public String format(Object value) {
        return base.format(value);
    }

    @Override
    public String toString() {
        return "boolean";
    }

    public static class Module extends SMVType {
        private final List<SVariable> parameters;
        private final String moduleName;

        public Module(String name, List<SVariable> moduleParameter) {
            this.moduleName = name;
            this.parameters = moduleParameter;
        }

        @Override
        public String toString() {
            return String.format("%s(%s)",
                    moduleName,
                    parameters.stream()
                            .map(v -> v.name)
                            .reduce((a, b) -> a + ", " + b).get());
        }
    }
}
