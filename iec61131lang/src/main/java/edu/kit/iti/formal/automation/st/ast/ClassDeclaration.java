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

import edu.kit.iti.formal.automation.oo.OOUtils;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (20.02.17)
 * @see OOUtils for convenient methods to access class information
 */

@Data
@EqualsAndHashCode(exclude = "methods", callSuper = true)
@NoArgsConstructor
public class ClassDeclaration extends Classifier<ParserRuleContext> {
    @NotNull
    private IdentifierPlaceHolder<ClassDeclaration> parent = new IdentifierPlaceHolder<>();
    @NotNull
    private List<MethodDeclaration> methods = new ArrayList<>();
    private boolean final_ = false;
    private boolean abstract_ = false;

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public void setParent(String parent) {
        this.parent.setIdentifier(parent);
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return The parent class. Return null if the class has no parent.
     */
    public ClassDeclaration getParentClass() {
        return parent.getIdentifiedObject();
    }

    public boolean hasParentClass() {
        return getParentClass() != null;
    }

    @Override
    public ClassDeclaration copy() {
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
