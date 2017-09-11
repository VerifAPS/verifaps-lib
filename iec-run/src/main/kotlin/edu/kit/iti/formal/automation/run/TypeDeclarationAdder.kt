package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.scope.GlobalScope
import edu.kit.iti.formal.automation.scope.LocalScope
import edu.kit.iti.formal.automation.st.ast.TypeDeclaration
import java.util.*

class TypeDeclarationAdder(definitionScopeStack: Stack<LocalScope>) {
    private val typeDeclarations: MutableList<TypeDeclaration<*>> = mutableListOf()

    fun postpone(typeDeclaration: TypeDeclaration<*>) {
        typeDeclarations.add(typeDeclaration)
    }

    fun addToGlobalScope(globalScope: GlobalScope) {
        typeDeclarations.forEach { globalScope.registerType(it) }
        typeDeclarations.retainAll(listOf())
    }
}