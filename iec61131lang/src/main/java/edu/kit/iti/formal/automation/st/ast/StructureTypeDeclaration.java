package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.RecordType;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.HashMap;
import java.util.Map;

import java.util.List;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class StructureTypeDeclaration extends TypeDeclaration<StructureInitialization> {
    Map<String, TypeDeclaration> fields = new HashMap<>();

    /**
     * <p>addField.</p>
     *
     * @param s a {@link java.lang.String} object.
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     */
    public void addField(String s, TypeDeclaration ast) {
        fields.put(s, ast);
    }

    public StructureTypeDeclaration(String typeName, List<VariableDeclaration> fields) {
        super(typeName);
        fields.forEach(this.fields::add);
    }

    /** {@inheritDoc} */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public Any getDataType(GlobalScope globalScope) {
        RecordType rt = new RecordType(getTypeName());
        for(Map.Entry<String, TypeDeclaration> s: fields.entrySet())
            rt.addField(s.getKey(), s.getValue().getDataType(globalScope));
        setBaseType(rt);
        return rt;
    }

    @Override public StructureTypeDeclaration copy() {
        StructureTypeDeclaration t = new StructureTypeDeclaration();
        t.setRuleContext(getRuleContext());
        t.initialization = Utils.copyNull(initialization);
        t.fields = new HashMap<>(fields);
        t.typeName = typeName;
        t.baseType = baseType;
        t.baseTypeName = baseTypeName;
        return t;
    }

}
