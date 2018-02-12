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
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
@NoArgsConstructor
public class StructureInitialization extends Initialization {
    private Map<String, Initialization> initValues = new HashMap<>();
    private String structureName;

    public StructureInitialization(List<Map.Entry<String, Initialization>> initEntries) {
        initEntries.forEach(entry -> initValues.put(entry.getKey(), entry.getValue()));
    }

    /**
     * <p>Getter for the field <code>initValues</code>.</p>
     *
     * @return a {@link java.util.Map} object.
     */
    public Map<String, Initialization> getInitValues() {
        return initValues;
    }

    /**
     * <p>Setter for the field <code>initValues</code>.</p>
     *
     * @param initValues a {@link java.util.Map} object.
     */
    public void setInitValues(Map<String, Initialization> initValues) {
        this.initValues = initValues;
    }

    /**
     * <p>addField.</p>
     *
     * @param s    a {@link java.lang.String} object.
     * @param init a {@link edu.kit.iti.formal.automation.st.ast.Initialization} object.
     */
    public void addField(String s, Initialization init) {
        initValues.put(s, init);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Any dataType(Scope localScope)
            throws VariableNotDefinedException, TypeConformityException {
        //TODO
        return null;
    }

    @Override
    public StructureInitialization copy() {
        StructureInitialization st = new StructureInitialization();
        st.structureName = structureName;
        st.initValues = new HashMap<>(initValues);
        return st;
    }
}
