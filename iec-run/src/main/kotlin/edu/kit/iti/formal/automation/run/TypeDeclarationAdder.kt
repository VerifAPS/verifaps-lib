package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.scope.GlobalScope
import edu.kit.iti.formal.automation.st.ast.TypeDeclaration

/**
 * ugly way for making adding TypeDeclarations possible, before the @see{Runtime}-Visitor as visited a scoped Element.
 * with .queueDeclaration() a typeDeclaration can be added to the queue;
 * with .addQueuedDeclarations() the queued declarations will be added to the global scope.
 */
class TypeDeclarationAdder {
    private val typeDeclarations: MutableList<TypeDeclaration<*>> = mutableListOf()

    /**
     * queue [typeDeclaration] for addition to the global scope.
     */
    fun queueDeclaration(typeDeclaration: TypeDeclaration<*>) {
        typeDeclarations.add(typeDeclaration)
    }

    /**
     * add queued type declarations to the [globalScope]
     */
    fun addQueuedDeclarations(globalScope: GlobalScope) {
        typeDeclarations.forEach { globalScope.registerType(it) }
        typeDeclarations.retainAll(listOf())
    }
}