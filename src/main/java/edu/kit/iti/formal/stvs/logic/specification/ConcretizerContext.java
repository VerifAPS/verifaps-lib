package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Value;

import java.util.HashMap;

/**
 * Created by bal on 09.01.17.
 */
public class ConcretizerContext {
    private HashMap<IOVariable, Value> ioVars;
    private HashMap<String, Value> constraintVars;


    public HashMap<IOVariable, Value> getIoVars() {
        return ioVars;
    }

    public HashMap<String, Value> getConstraintVars() {
        return constraintVars;
    }
}
