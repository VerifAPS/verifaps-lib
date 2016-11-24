package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;

import java.util.TreeMap;

/**
 * Created by weigl on 24.11.16.
 */
public class VariableScope extends TreeMap<String, VariableDeclaration> {
    public void add(VariableDeclaration var) {
        put(var.getName(), var);
    }
}
