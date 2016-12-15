package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SVariable;

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
public class SpecificationInterfaceMisMatchException extends RuntimeException {
    public SpecificationInterfaceMisMatchException() {
        super();
    }

    public SpecificationInterfaceMisMatchException(String message) {
        super(message);
    }

    public SpecificationInterfaceMisMatchException(String message, Throwable cause) {
        super(message, cause);
    }

    public SpecificationInterfaceMisMatchException(Throwable cause) {
        super(cause);
    }

    protected SpecificationInterfaceMisMatchException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public SpecificationInterfaceMisMatchException(SMVModule code, SVariable v) {
        super(String.format("Could not find variable '%s' in module: %s", v.name, code.getName()));
    }
}
