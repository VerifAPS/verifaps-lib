package edu.kit.iti.formal.automation.operators;

import edu.kit.iti.formal.automation.datatypes.Any;

public interface Operator {
    String symbol();
    Any[] getExpectedDataTypes();
}

