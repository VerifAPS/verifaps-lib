package edu.kit.iti.formal.automation.st0.trans;

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.datatypes.IECArray;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

/**
 * Created by weigl on 03/10/14.
 */
public class ArrayEmbedder extends AstMutableVisitor {
    private Scope currentScope;


    @Override
    public Object defaultVisit(Visitable visitable) {
        return visitable;
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        currentScope = (Scope) programDeclaration.getScope().accept(this);
        ProgramDeclaration pd = (ProgramDeclaration) super.visit(programDeclaration);
        pd.setScope(currentScope);
        return pd;
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        currentScope = (Scope) functionDeclaration.getScope().accept(this);
        ProgramDeclaration pd = (ProgramDeclaration) super.visit(functionDeclaration);
        pd.setScope(currentScope);
        return pd;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        currentScope = (Scope) functionBlockDeclaration.getScope().accept(this);
        ProgramDeclaration pd = (ProgramDeclaration) super.visit(functionBlockDeclaration);
        pd.setScope(currentScope);
        return pd;
    }

    @Override
    public Object visit(ArrayTypeDeclaration arrayType) {
        return super.visit(arrayType);
    }


    @Override
    public Object visit(SymbolicReference symbolicReference) {
        String identifier = symbolicReference.getIdentifier();

        if (symbolicReference.getSubscripts() != null) {
            IntegerExpressionEvaluator iee = new IntegerExpressionEvaluator(currentScope);
            StringBuilder sb = new StringBuilder(identifier);

            for (Expression expression : symbolicReference.getSubscripts()) {
                long pos = (Long) expression.accept(iee);
                sb.append("_").append(pos);
            }
            VariableDeclaration vd = currentScope.getVariable(symbolicReference);
            IECArray atd = (IECArray) vd.getDataType();
            VariableDeclaration vdnew = new VariableDeclaration(sb.toString(),
                    vd.getType(),
                    vd.getDataType());
            vdnew.setDataType(atd.getFieldType());
            currentScope.add(vdnew);
            return new SymbolicReference(sb.toString());
        } else {
            return super.visit(symbolicReference);
        }
    }

    public static ST0Transformation getTransformation() {
        return state -> {
            ArrayEmbedder ae = new ArrayEmbedder();
            state.theProgram = (ProgramDeclaration) state.theProgram.accept(ae);
        };
    }
}
