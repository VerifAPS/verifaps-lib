package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 13.06.14.
 */
public class StructureTypeDeclaration extends TypeDeclaration<StructureInitialization> {
    Map<String, TypeDeclaration> fields = new HashMap<>();
    public void addField(String s, TypeDeclaration ast) {
        fields.put(s,ast);
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
