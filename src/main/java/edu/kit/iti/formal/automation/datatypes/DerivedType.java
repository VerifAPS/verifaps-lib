package edu.kit.iti.formal.automation.datatypes;

/**
 * @author weigla
 * @date 25.06.2014
 */
public class DerivedType extends Any {
    private Any derivedFrom;
    private String derivedFromName;

    public DerivedType(String derivedFromName) {
        super(derivedFromName);
        this.derivedFromName = derivedFromName;
    }

    @Override
    public String repr(Object obj) {
        return "n/a";
    }
}
