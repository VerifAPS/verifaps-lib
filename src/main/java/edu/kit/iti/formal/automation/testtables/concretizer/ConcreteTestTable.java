package edu.kit.iti.formal.automation.testtables.concretizer;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public class ConcreteTestTable {
    private List<TreeMap<String, Object>> data = new LinkedList<>();

    public int getLength() {
        return data.size();
    }

    public int getNumOfVars() {
        return data.get(0).size();
    }


}
