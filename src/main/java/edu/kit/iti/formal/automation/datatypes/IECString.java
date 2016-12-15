package edu.kit.iti.formal.automation.datatypes;

public abstract class IECString extends Any {
    public final static String STRING_8BIT = new String();
    public final static WString STRING_16BIT = new WString();


    public final static class WString extends IECString {
        @Override
        public java.lang.String repr(Object obj) {
            return "WSTRING#\"" + obj + "\"";
        }


        @Override
        public <T> T accept(DataTypeVisitor<T> visitor) {
            return visitor.visit(this);
        }
    }

    public final static class String extends IECString {
        @Override
        public java.lang.String repr(Object obj) {
            return "WSTRING#'" + obj + "'";
        }

        @Override
        public <T> T accept(DataTypeVisitor<T> visitor) {
            return visitor.visit(this);
        }
    }


}