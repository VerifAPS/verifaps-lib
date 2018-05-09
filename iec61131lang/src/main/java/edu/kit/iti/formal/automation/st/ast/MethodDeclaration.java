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

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (20.02.17)
 */

@Data
@EqualsAndHashCode(exclude = "parent", callSuper = false)
@ToString(callSuper = false, exclude = "parent")
public class MethodDeclaration extends Top<ParserRuleContext> implements Invocable, Identifiable {
    protected IdentifierPlaceHolder<AnyDt> returnType = new IdentifierPlaceHolder<>();
    protected String name;
    protected StatementList stBody = new StatementList();
    private Scope scope = new Scope();
    private Classifier<?> parent;
    private AccessSpecifier accessSpecifier = AccessSpecifier.defaultAccessSpecifier();
    private boolean final_ = false;
    private boolean abstract_ = false;
    private boolean override = false;

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public MethodDeclaration copy() {
        MethodDeclaration md = new MethodDeclaration();
        md.accessSpecifier = accessSpecifier;
        md.final_ = final_;
        md.abstract_ = abstract_;
        md.override = override;
        md.scope = scope.copy();
        md.name = name;
        md.returnType = returnType.copy();
        return md;
    }

    @Override
    public String getIdentifier() {
        return getName();
    }

    public String getReturnTypeName() {
        if (returnType.getIdentifier() == null)
            return "VOID";
        return returnType.getIdentifier();
    }

    public void setReturnTypeName(String rt) {
        returnType.setIdentifier(rt);
    }

    public AnyDt getReturnType() {
        return returnType.getIdentifiedObject();
    }

    public void setReturnType(AnyDt rt) {
        returnType.setIdentifiedObject(rt);
    }

}
