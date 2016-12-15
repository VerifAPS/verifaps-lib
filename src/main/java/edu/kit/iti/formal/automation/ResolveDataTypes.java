package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import jdk.nashorn.internal.objects.Global;

/**
 * @author Alexander Weigl
 * @version 1 (25.11.16)
 */
public class ResolveDataTypes extends DefaultVisitor<Object> {
    private GlobalScope scope = new GlobalScope();

    private boolean registerPhase = true;

    public ResolveDataTypes() {
    }

    public ResolveDataTypes(GlobalScope scope) {
        this.scope = scope;
    }


    public static GlobalScope resolve(TopLevelElements tle) {
        GlobalScope globalScope = GlobalScope.defaultScope();
        ResolveDataTypes rdt = new ResolveDataTypes(globalScope);
        tle.visit(rdt);
        rdt.registerPhase = false;
        tle.visit(rdt);
        return globalScope;
    }

    private Any resolve(String name) {
        return scope.resolveDataType(name);
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.setGlobalScope(scope);
        if (registerPhase)
            scope.registerProgram(programDeclaration);
        else
            programDeclaration.getLocalScope().visit(this);
        return super.visit(programDeclaration);
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.setGlobalScope(scope);
        if (registerPhase)
            scope.registerFunction(functionDeclaration);
        else {
            functionDeclaration.setReturnType(
                    resolve(functionDeclaration.getReturnTypeName()));
            functionDeclaration.getLocalScope().visit(this);
        }
        return null;
    }

    @Override
    public Object visit(LocalScope localScope) {
        localScope.getLocalVariables().values().forEach(
                vd -> vd.setDataType(resolve(vd.getDataTypeName()))
        );
        return null;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.setGlobalScope(scope);
        if (registerPhase)
            scope.registerFunctionBlock(functionBlockDeclaration);
        else
            functionBlockDeclaration.getLocalScope().visit(this);
        return super.visit(functionBlockDeclaration);
    }


    @Override
    public Object visit(SubRangeTypeDeclaration subRangeTypeDeclaration) {
        if (registerPhase) scope.registerType(subRangeTypeDeclaration);
        return null;
    }

    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        if (registerPhase) scope.registerType(simpleTypeDeclaration);
        return null;
    }

    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        if (!registerPhase) {//every data type is registered
            variableDeclaration.setDataType(
                    variableDeclaration.getTypeDeclaration().getDataType(scope));
        }
        return null;
    }


    @Override
    public Object visit(PointerTypeDeclaration ptd) {
        if (registerPhase) scope.registerType(ptd);
        return null;
    }

    @Override
    public Object visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        if (registerPhase) scope.registerType(arrayTypeDeclaration);
        return null;
    }

    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        if (registerPhase) scope.registerType(enumerationTypeDeclaration);
        return null;
    }

    @Override
    public Object visit(StringTypeDeclaration stringTypeDeclaration) {
        if (registerPhase) scope.registerType(stringTypeDeclaration);

        return null;
    }

    @Override
    public Object visit(TypeDeclarations typeDeclarations) {
        for (TypeDeclaration td : typeDeclarations)
            td.visit(this);
        return null;
    }

    @Override
    public Object visit(StructureTypeDeclaration structureTypeDeclaration) {
        if (registerPhase) scope.registerType(structureTypeDeclaration);
        return null;
    }

}
