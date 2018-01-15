package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.scope.GlobalScope
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.StructureTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.TypeDeclaration

/**
 * ugly way for making adding TypeDeclarations possible, before the @see{Runtime}-Visitor as visited a scoped Element.
 * with .queueTypeDeclaration() a typeDeclaration can be added to the queue;
 * with .addQueuedDeclarations() the queued declarations will be added to the global scope.
 */
class TypeDeclarationAdder {
    private val typeDeclarations: MutableList<TypeDeclaration<*>> = mutableListOf()
    public val functionBlockDeclarations: MutableList<FunctionBlockDeclaration> = mutableListOf()
    private  val functionDeclarations: MutableList<FunctionDeclaration> = mutableListOf()
    private val structureTypeDeclarations: MutableList<StructureTypeDeclaration> = mutableListOf()

    /**
     * queue [typeDeclaration] for addition to the global scope.
     */
    fun queueTypeDeclaration(typeDeclaration: TypeDeclaration<*>) {
        typeDeclarations.add(typeDeclaration)
    }

    fun queueFunctionBlockDeclaration(functionBlockDeclaration: FunctionBlockDeclaration) {
        functionBlockDeclarations.add(functionBlockDeclaration)
    }

    fun queueFunctionDeclaration(functionDeclaration: FunctionDeclaration) {
        functionDeclarations.add(functionDeclaration)
    }

    fun queueTypeStructureDeclaration(structureTypeDeclaration: StructureTypeDeclaration) {
        structureTypeDeclarations.add(structureTypeDeclaration)
    }

    /**
     * add queued type declarations to the [globalScope]
     */
    fun addQueuedDeclarations(globalScope: GlobalScope): TypeDeclarationAdder {
        typeDeclarations.forEach { globalScope.registerType(it) }
        typeDeclarations.retainAll(emptyList())

        functionBlockDeclarations.forEach { globalScope.registerFunctionBlock(it) }
        functionBlockDeclarations.retainAll(emptyList())


        functionDeclarations.forEach { globalScope.registerFunction(it) }
        functionDeclarations.retainAll(emptyList())

        structureTypeDeclarations.forEach { globalScope.registerType(it) }
        structureTypeDeclarations.retainAll(emptyList())
        return this
    }
}