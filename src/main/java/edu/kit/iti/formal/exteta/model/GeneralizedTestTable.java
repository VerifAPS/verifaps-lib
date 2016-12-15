package edu.kit.iti.formal.exteta.model;

import java.util.*;

import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.exteta.io.IOFacade;
import edu.kit.iti.formal.exteta.schema.ConstraintVariable;
import edu.kit.iti.formal.exteta.schema.IoVariable;
import edu.kit.iti.formal.exteta.schema.Variable;
import edu.kit.iti.formal.smv.ast.SVariable;

public class GeneralizedTestTable {
    private Region region;

    private final LinkedHashMap<String, IoVariable> ioVariables = new LinkedHashMap<>();
    private final Map<String, ConstraintVariable> constraintVariables = new HashMap<>();
    private final Map<String, SVariable> variableMap = new HashMap<>();
    private final Properties properties = new Properties(System.getProperties());
    private final Map<String, FunctionDeclaration> functions = new HashMap<>();
    private String name;

    public Map<String, IoVariable> getIoVariables() {
        return ioVariables;
    }

    public Map<String, ConstraintVariable> getConstraintVariable() {
        return constraintVariables;
    }

    public void setRegion(Region region) {
        this.region = region;
    }

    public Region getRegion() {
        return region;
    }

    public SVariable getSMVVariable(String text) {
        variableMap.computeIfAbsent(text,
                (k) -> IOFacade.asSMVVariable(getVariable(text)));
        return variableMap.get(text);
    }

    private Variable getVariable(String text) {
        IoVariable a = ioVariables.get(text);
        ConstraintVariable b = constraintVariables.get(text);
        if (a != null)
            return a;
        else
            return b;
    }

    public void add(IoVariable v) {
        ioVariables.put(v.getName(), v);
    }

    public void add(ConstraintVariable v) {
        constraintVariables.put(v.getName(), v);
    }

    public void addOption(String key, String value) {
        properties.put(key, value);
    }


    public void addFunctions(List<TopLevelElement> file) {
        for (TopLevelElement e : file) {
            functions.put(e.getBlockName(), (FunctionDeclaration) e);
        }
    }

    public String getName() {
        return name;
    }

    public IoVariable getIoVariables(int i) {
        int k = 0;
        for (IoVariable v : ioVariables.values()) {
            if (k++ == i) return v;
        }
        return null;
    }

    public void setName(String name) {
        this.name = name;
    }
}
