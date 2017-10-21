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
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

/**
 * @author Alexander Weigl
 * @version 1 (20.02.17)
 */

@EqualsAndHashCode
@ToString
@Data
public class MethodDeclaration extends FunctionDeclaration {
    private AccessSpecifier accessSpecifier = AccessSpecifier.defaultAccessSpecifier();
    private boolean final_ = false;
    private boolean abstract_ = false;
    private boolean override = false;

    @Override
    public String getReturnTypeName() {
        if (returnType.getIdentifier() == null)
            return "VOID";
        return super.getReturnTypeName();
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public void setName(String n) {
        setFunctionName(n);
    }

    @Override
    public MethodDeclaration copy() {
        MethodDeclaration md = new MethodDeclaration();
        md.accessSpecifier = accessSpecifier;
        md.final_ = final_;
        md.abstract_ = abstract_;
        md.override = override;
        md.localScope = localScope.copy();
        md.functionName = functionName;
        md.returnType = returnType.copy();
        return md;
    }
}
