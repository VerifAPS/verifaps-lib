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

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * @author Alexander Weigl
 * @version 1 (20.02.17)
 */
public class MethodDeclaration extends Top {
    private ClassDeclaration classDeclaration;
    private LocalScope localScope;
    private StatementList body;

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return null;
    }

    public LocalScope getLocalScope() {
        return localScope;
    }

    public void setBody(StatementList body) {
        this.body = body;
    }

    public StatementList getBody() {
        return body;
    }

    public ClassDeclaration getClassDeclaration() {
        return classDeclaration;
    }

    public MethodDeclaration setClassDeclaration(ClassDeclaration classDeclaration) {
        this.classDeclaration = classDeclaration;
        return this;
    }

    public MethodDeclaration setLocalScope(LocalScope localScope) {
        this.localScope = localScope;
        return this;
    }
}
