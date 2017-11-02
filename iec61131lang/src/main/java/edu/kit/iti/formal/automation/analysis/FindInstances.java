/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

package edu.kit.iti.formal.automation.analysis;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import lombok.RequiredArgsConstructor;

/**
 * Visitor which finds all instances of classes and FBs and adds them to the global scope.
 *
 * @author Augusto Modanese
 */
@RequiredArgsConstructor
public class FindInstances extends AstVisitor {
    private final InstanceScope instanceScope;

    @Override
    public Object visit(LocalScope localScope) {
        localScope.forEach(variableDeclaration -> {
            if (variableDeclaration.isInput() || variableDeclaration.isOutput() || variableDeclaration.isInOut())
                return;
            Any dataType = variableDeclaration.getDataType();
            // Function blocks extend classes, so they must go first (more specific)
            if (dataType instanceof FunctionBlockDataType)
                instanceScope.registerFunctionBlockInstance(((FunctionBlockDataType) dataType).getFunctionBlock(),
                        variableDeclaration);
            else if (dataType instanceof ClassDataType)
                instanceScope.registerClassInstance(((ClassDataType) dataType).getClazz(), variableDeclaration);
        });
        return super.visit(localScope);
    }
}
