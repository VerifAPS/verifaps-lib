package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import lombok.Data;
import lombok.EqualsAndHashCode;
import org.antlr.v4.runtime.ParserRuleContext;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (31.01.18)
 */
@Data
@EqualsAndHashCode(callSuper = true, exclude = "methods")
public abstract class Classifier<T extends ParserRuleContext> extends TopLevelScopeElement<T> {
    protected List<IdentifierPlaceHolder<InterfaceDeclaration>> interfaces = new ArrayList<>();
    protected List<MethodDeclaration> methods = new ArrayList<>();
    protected String name = "";

    public void addExtendsOrImplements(String interfaze) {
        interfaces.add(new IdentifierPlaceHolder<>(interfaze));
    }

    public void setMethods(List<MethodDeclaration> methods) {
        for (MethodDeclaration methodDeclaration : methods) {
            methodDeclaration.setParent(this);
            methodDeclaration.getScope().setParent(scope);
        }
        this.methods = methods;
    }


    @Override
    public String getIdentifier() {
        return name;
    }
}
