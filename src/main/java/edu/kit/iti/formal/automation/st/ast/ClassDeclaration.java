package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (20.02.17)
 */
public class ClassDeclaration extends TopLevelScopeElement
{
    private List<MethodDeclaration> methods = new ArrayList<>();
    private String name;

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return null;
    }

    public List<MethodDeclaration> getMethods() {
        return methods;
    }

    public ClassDeclaration setMethods(List<MethodDeclaration> methods) {
        this.methods = methods;
        return this;
    }

    @Override
    public String getBlockName() {
        return name;
    }

    public ClassDeclaration setBlockName(String name) {
        this.name = name;
        return this;
    }
}
