package edu.kit.iti.formal.automation.exceptions;

/**
 * @author Alexander Weigl
 * @version 1 (15.12.16)
 */
public class UnknownDatatype extends RuntimeException {
    public UnknownDatatype(String s, NullPointerException e) {
        super(s, e);
    }
}
