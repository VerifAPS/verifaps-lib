package edu.kit.iti.formal.automation.datatypes;

public abstract class AnyReal extends AnyNum {

    public static final LReal LREAL = new LReal();
    public static final Real REAL = new Real();

    @Override
    public String repr(Object obj) {
        Double d = (Double) obj;
        return getClass().getName().toUpperCase() + "#" + d;
    }


    public static class Real extends AnyReal {
    }

    public static class LReal extends AnyReal {
    }

}