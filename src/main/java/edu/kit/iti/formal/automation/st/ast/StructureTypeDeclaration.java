package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.RecordType;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 13.06.14.
 */
public class StructureTypeDeclaration extends TypeDeclaration<StructureInitialization> {
    Map<String, TypeDeclaration> fields = new HashMap<>();

    public void addField(String s, TypeDeclaration ast) {
        fields.put(s, ast);
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Any getDataType(GlobalScope globalScope) {
        RecordType rt = new RecordType(getTypeName());
        for(Map.Entry<String, TypeDeclaration> s: fields.entrySet())
            rt.addField(s.getKey(), s.getValue().getDataType(globalScope));
        setBaseType(rt);
        return rt;
    }
}
