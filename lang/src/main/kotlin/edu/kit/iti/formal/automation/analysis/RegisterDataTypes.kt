package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (25.06.17)
 */
@Suppress("PARAMETER_NAME_CHANGED_ON_OVERRIDE")
class RegisterDataTypes(val globalScope: Scope) : AstVisitorWithScope<Unit>() {
    init {
        scope = globalScope
    }

    override fun defaultVisit(obj: Any) {}

    override fun visit(elements: PouElements) {
        super.visit(elements)
    }

    override fun visit(pd: ProgramDeclaration) {
        scope.registerProgram(pd)
        goIntoScope(pd)
        pd.actions.forEach { a -> pd.scope.registerAction(a) }
        goOutoScope()
    }

    override fun visit(fbd: FunctionBlockDeclaration) {
        scope.registerFunctionBlock(fbd)
        goIntoScope(fbd)
        fbd.actions.forEach { scope.registerAction(it) }
        fbd.methods.forEach { scope.registerMethod(it); it.scope.parent = scope }
        goOutoScope()
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        scope.registerFunction(functionDeclaration)
        goIntoScope(functionDeclaration)
        goOutoScope()
    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration) {
        scope.registerType(subRangeTypeDeclaration)
    }

    override fun visit(variableDeclaration: VariableDeclaration) {
        //weigl: do not register anonymous datatype, or references to data types.
        /*
        if (variableDeclaration.getTypeDeclaration() instanceof ArrayTypeDeclaration)
            variableDeclaration.getTypeDeclaration().accept(this);
        return super.visit(variableDeclaration);
        */

    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        scope.registerType(simpleTypeDeclaration)
        //super.visit(simpleTypeDeclaration)
    }

    override fun visit(ptd: PointerTypeDeclaration) {
        scope.registerType(ptd)
        return super.visit(ptd)
    }

    override fun visit(clazz: ClassDeclaration) {
        scope.registerClass(clazz)
        goIntoScope(clazz)
        clazz.methods.forEach { scope.registerMethod(it); it.scope.parent = scope }
        goOutoScope()
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        //goIntoScope(interfaceDeclaration)
        scope.registerInterface(interfaceDeclaration)
        //super.visit(interfaceDeclaration)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {
        scope.registerType(arrayTypeDeclaration)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        scope.registerType(enumerationTypeDeclaration)

    }

    /**
     * {@inheritDoc}
     */
    override fun visit(stringTypeDeclaration: StringTypeDeclaration) {
        scope.registerType(stringTypeDeclaration)

    }

    override fun visit(typeDeclarations: TypeDeclarations) {
        for (td in typeDeclarations)
            td.accept(this)

    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        scope.registerType(structureTypeDeclaration)

    }

    override fun visit(gvl: GlobalVariableListDeclaration) {
        scope.addVariables(gvl.scope)
        gvl.scope = scope // global variables does not open an own scope.
        //return super.visit(gvl)

    }

    private fun goIntoScope(hasScope: HasScope) {
        if (scope != null)
            hasScope.scope.parent = scope
        scope = hasScope.scope
    }

    private fun goOutoScope() {
        scope = if (scope.parent != null) scope.parent!! else globalScope
    }
}
