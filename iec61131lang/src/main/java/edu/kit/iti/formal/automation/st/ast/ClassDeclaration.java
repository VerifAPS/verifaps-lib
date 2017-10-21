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

import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (20.02.17)
 */

@Data
@EqualsAndHashCode
@ToString
public class ClassDeclaration extends TopLevelScopeElement {
    private String name;
    private boolean final_ = false;
    private boolean abstract_ = false;
    private IdentifierPlaceHolder<ClassDeclaration> parent = new IdentifierPlaceHolder<>();
    private List<IdentifierPlaceHolder<InterfaceDeclaration>> interfaces = new ArrayList<>();
    private List<MethodDeclaration> methods = new ArrayList<>();

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override public String getIdentifier() {
        return name;
    }

    public void setParent(String parent) {
        this.parent.setIdentifier(parent);
    }

    public void addImplements(String interfaze) {
        interfaces.add(new IdentifierPlaceHolder<>(interfaze));
    }

    public void addImplements(List<String> interfaceList) {
        interfaceList.forEach(i -> addImplements(i));
    }

    @Override public ClassDeclaration copy() {
        ClassDeclaration c = new ClassDeclaration();
        c.name = name;
        c.final_ = final_;
        c.abstract_ = abstract_;
        c.parent = parent.copy();
        interfaces.forEach(i -> c.interfaces.add(i.copy()));
        methods.forEach(m -> c.methods.add(m.copy()));
        return c;
    }
}
