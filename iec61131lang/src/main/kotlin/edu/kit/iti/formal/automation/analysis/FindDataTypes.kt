package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (25.06.17)
 */
class FindDataTypes(val globalScope: Scope) : AstVisitorWithScope<Any>() {
    override fun visit(pd: ProgramDeclaration): Any? {
        goIntoScope(pd)
        scope.registerProgram(pd)
        pd.actions.forEach { n, a -> pd.scope.registerAction(a) }
        return null
    }

    override fun visit(fbd: FunctionBlockDeclaration): Any? {
        goIntoScope(fbd)
        scope.registerFunctionBlock(fbd)
        fbd.actions.forEach { scope.registerAction(it)  }
        fbd.methods.forEach { scope.registerMethod(it); }
        goOutoScope()
        return null
    }

    override fun visit(functionDeclaration: FunctionDeclaration): Any? {
        goIntoScope(functionDeclaration)
        scope.registerFunction(functionDeclaration)
        goOutoScope()
        return null
    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): Any? {
        scope.registerType(subRangeTypeDeclaration)
        return null
    }

    override fun visit(variableDeclaration: VariableDeclaration): Any? {
        //weigl: do not register anonymous datatype, or references to data types.
        /*
        if (variableDeclaration.getTypeDeclaration() instanceof ArrayTypeDeclaration)
            variableDeclaration.getTypeDeclaration().accept(this);
        return super.visit(variableDeclaration);
        */
        return null
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): Any? {
        scope.registerType(simpleTypeDeclaration)
        return null //super.visit(simpleTypeDeclaration)
    }

    override fun visit(ptd: PointerTypeDeclaration): Any? {
        scope.registerType(ptd)
        return super.visit(ptd)
    }

    override fun visit(clazz: ClassDeclaration): Any? {
        scope.registerClass(clazz)
        goIntoScope(clazz)
        clazz.methods.forEach { scope.registerMethod(it) }
        goOutoScope()
        return super.visit(clazz)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): Any? {
        //goIntoScope(interfaceDeclaration)
        scope.registerInterface(interfaceDeclaration)
        return null //super.visit(interfaceDeclaration)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): Any? {
        scope.registerType(arrayTypeDeclaration)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): Any? {
        scope.registerType(enumerationTypeDeclaration)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(stringTypeDeclaration: StringTypeDeclaration): Any? {
        scope.registerType(stringTypeDeclaration)
        return null
    }

    override fun visit(typeDeclarations: TypeDeclarations): Any? {
        for (td in typeDeclarations)
            td.accept(this)
        return null
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): Any? {
        scope.registerType(structureTypeDeclaration)
        return null
    }

    override fun visit(gvl: GlobalVariableListDeclaration): Any? {
        gvl.scope = scope // global variables does not open an own scope.
        scope.addVariables(gvl.scope)
        //return super.visit(gvl)
        return null
    }

    private fun goIntoScope(hasScope: HasScope) {
        hasScope.scope.parent = scope
        scope = hasScope.scope
    }

    private fun goOutoScope() {
        scope = if (scope.parent != null) scope.parent!! else globalScope
    }
}
