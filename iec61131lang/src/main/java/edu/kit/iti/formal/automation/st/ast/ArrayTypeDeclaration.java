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
import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.datatypes.IECArray;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.EqualsAndHashCode;
import lombok.ToString;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@EqualsAndHashCode
@ToString
public class ArrayTypeDeclaration extends TypeDeclaration<ArrayInitialization> {
    private List<Range> ranges = new ArrayList<>();

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public ArrayTypeDeclaration copy() {
        ArrayTypeDeclaration atd = new ArrayTypeDeclaration();
        atd.setRuleContext(getRuleContext());
        ranges.forEach(range -> atd.ranges.add(range.copy()));
        atd.typeName = typeName;
        atd.baseType = baseType;
        atd.baseTypeName = baseTypeName;
        atd.initialization = Utils.copyNull(initialization);
        return atd;
    }

    /**
     * <p>addSubRange.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Range} object.
     */
    public void addSubRange(Range ast) {
        ranges.add(ast);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Any getDataType(GlobalScope globalScope) {
        super.getDataType(globalScope);
        Any dt = DataTypes.getDataType(getBaseTypeName());
        IECArray array = new IECArray(getTypeName(), getBaseType(), ranges);
        setBaseType(dt);
        return array;
    }
}
