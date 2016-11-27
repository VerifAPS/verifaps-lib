package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.datatypes.IECArray;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

/**
 * Created by weigl on 03/10/14.
 */
public class ArrayEmbedder extends AstCopyVisitor {
    private LocalScope currentScope;

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        currentScope = (LocalScope) programDeclaration.getLocalScope().visit(this);
        ProgramDeclaration pd = (ProgramDeclaration) super.visit(programDeclaration);
        pd.setLocalScope(currentScope);
        return pd;
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        currentScope = (LocalScope) functionDeclaration.getLocalScope().visit(this);
        ProgramDeclaration pd = (ProgramDeclaration) super.visit(functionDeclaration);
        pd.setLocalScope(currentScope);
        return pd;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        currentScope = (LocalScope) functionBlockDeclaration.getLocalScope().visit(this);
        ProgramDeclaration pd = (ProgramDeclaration) super.visit(functionBlockDeclaration);
        pd.setLocalScope(currentScope);
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
                long pos = (Long) expression.visit(iee);
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

}
