package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;

import java.util.Map;

/**
 * Created by bal on 09.01.17.
 */
public class ConcretizerContext {
    private Map<String, Type> variableTypes;
    private Map<String, Value> variableValues;
    private Map<String, Value> constraintVars;


    public Map<String, Value> getVariableValues() {
        return variableValues;
    }

    public Map<String, Value> getConstraintVars() {
        return constraintVars;
    }
}
