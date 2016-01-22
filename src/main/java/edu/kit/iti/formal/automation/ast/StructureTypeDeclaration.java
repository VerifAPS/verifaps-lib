package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 13.06.14.
 */
public class StructureTypeDeclaration extends TypeDeclaration<Object> {
    Map<String, TypeDeclaration> fields = new HashMap<>();

    public void addField(String s, SimpleTypeDeclaration ast) {

    }

    public void addField(String s, SubRangeDataType ast) {
    }

    public void addField(String s, ScalarValue<EnumerateType, String> enumeratedValue) {

    }

    public void addField(String s, ArrayTypeDeclaration ast) {

    }

    public void addField(String s, StructureInitialization ast) {

    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
