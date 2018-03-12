package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.smv.Printer;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class SMVType {
    public static final SMVType BOOLEAN = new SMVType(GroundDataType.BOOLEAN);
    public static final SMVType INT = new SMVType(GroundDataType.INT);
    public static final SMVType FLOAT = new SMVType(GroundDataType.FLOAT);

    protected GroundDataType baseType;

    public SMVType() {
    }

    public SMVType(GroundDataType b) {
        baseType = b;
    }

    public static SMVType infer(List<SMVType> list) {
        if(list.stream().allMatch(a->a.equals(list.get(0))))
            return list.get(0);
        return null;
    }

    public static SMVType infer(SMVType a, SMVType b) {
        if(a.equals(b))
            return a;

        return null;
    }

    public static SMVType unsigned(int i) {
        return new SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, i);
    }

    public static SMVType signed(int i) {
        return new SMVTypeWithWidth(GroundDataType.SIGNED_WORD, i);
    }

    public GroundDataType getBaseType() {
        return baseType;
    }

    public SMVType setBaseType(GroundDataType baseType) {
        this.baseType = baseType;
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof SMVType)) return false;

        SMVType smvType = (SMVType) o;

        return baseType == smvType.baseType;
    }

    public SLiteral valueOf(String value) {
        SLiteral l = new SLiteral();
        l.dataType = this;
        l.value = baseType.parse(value);
        return l;
    }

    public String format(Object value) {
        return baseType.format(value);
    }

    @Override
    public String toString() {
        return "boolean";
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
                    (baseType == GroundDataType.UNSIGNED_WORD
                            ? "unsigned" : "signed")
                    , width);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            if (!super.equals(o)) return false;

            SMVTypeWithWidth that = (SMVTypeWithWidth) o;

            if (getWidth() != that.getWidth()) return false;
            return getBaseType() == that.getBaseType();

        }

        @Override
        public int hashCode() {
            int result = super.hashCode();
            result = 31 * result + getWidth();
            result = 31 * result + getBaseType().hashCode();
            return result;
        }

        @Override
        public String format(Object value) {
            BigInteger bigInteger = BigInteger.ZERO;
            if (value instanceof String) {
                bigInteger = new BigInteger(value.toString());
            } else if (value instanceof Integer) {
                Integer integer = (Integer) value;
                bigInteger = BigInteger.valueOf((Integer) value);
            } else if (value instanceof Long) {
                bigInteger = BigInteger.valueOf((Long) value);
            } else if (value instanceof BigInteger)
                bigInteger = (BigInteger) value;

            return String.format("%s0%sd%d_%s",
                    (bigInteger.signum() < 0 ? "-" : ""),
                    (baseType == GroundDataType.SIGNED_WORD ? "s" : "u"),
                    width,
                    bigInteger.abs().toString());
        }
    }

    public static class EnumType extends SMVType {
        private List<String> values;

        public EnumType(List<String> id) {
            values = new ArrayList<>(id);
        }

        public SLiteral valueOf(String value) {
            SLiteral l = super.valueOf(value);
            if (!values.contains(l.value)) {
                throw new IllegalArgumentException();
            }
            return l;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            if (!super.equals(o)) return false;

            EnumType enumType = (EnumType) o;

            return values.equals(enumType.values);

        }

        @Override
        public int hashCode() {
            int result = super.hashCode();
            result = 31 * result + values.hashCode();
            return result;
        }

        public List<String> getValues() {
            return values;
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

    public static class Module extends SMVType {
        private final List<? extends SMVExpr> parameters;
        private final String moduleName;

        public Module(String name) {
            moduleName = name;
            parameters = new ArrayList<>();
        }


        public Module(String name, List<? extends SMVExpr> moduleParameter) {
            this.moduleName = name;
            parameters = moduleParameter;
        }

        public Module(String name, SVariable... variables) {
            this(name, Arrays.asList(variables));
        }

        @Override
        public String toString() {
            Printer printer = new Printer();
            return String.format("%s(%s)",
                    moduleName,
                    parameters.stream()
                            .map(v -> v.accept(printer))
                            .reduce((a, b) -> a + ", " + b).orElse(""));
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            if (!super.equals(o)) return false;

            Module module = (Module) o;

            if (!parameters.equals(module.parameters)) return false;
            return moduleName.equals(module.moduleName);

        }

        @Override
        public int hashCode() {
            int result = super.hashCode();
            result = 31 * result + parameters.hashCode();
            result = 31 * result + moduleName.hashCode();
            return result;
        }
    }

}