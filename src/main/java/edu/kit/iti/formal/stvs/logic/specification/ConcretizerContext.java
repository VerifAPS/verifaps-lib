package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Value;

import java.util.Map;

/**
 * Created by bal on 09.01.17.
 */
public class ConcretizerContext {
    private Map<IOVariable, Value> ioVars;
    private Map<String, Value> constraintVars;


    public Map<IOVariable, Value> getIoVars() {
        return ioVars;
    }

    public Map<String, Value> getConstraintVars() {
        return constraintVars;
    }
}
