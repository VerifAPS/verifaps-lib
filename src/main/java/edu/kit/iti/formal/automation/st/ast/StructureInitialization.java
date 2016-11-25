package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedinScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

/**
 * Created by weigl on 13.06.14.
 */
public class StructureInitialization extends Initialization {
    private Map<String, Initialization> initValues = new HashMap<>();
    private String structureName;


    public Map<String, Initialization> getInitValues() {
        return initValues;
    }

    public void setInitValues(Map<String, Initialization> initValues) {
        this.initValues = initValues;
    }

    public void addField(String s, Initialization init) {
        initValues.put(s, init);
    }

    public String getStructureName() {
        return structureName;
    }

    public void setStructureName(String structureName) {
        this.structureName = structureName;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Any dataType(LocalScope localScope) throws VariableNotDefinedinScope, TypeConformityException {
        //TODO
        return null;
    }
}
