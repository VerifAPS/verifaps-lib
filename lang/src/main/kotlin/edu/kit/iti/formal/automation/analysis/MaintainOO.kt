package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.02.19)
 */

class ResolveOO(val globalScope: edu.kit.iti.formal.automation.scope.Scope) : AstVisitorWithScope<Unit>() {
    private var clazz: ClassDeclaration? = null
    private var interfaze: InterfaceDeclaration? = null
    private var functionBlock: FunctionBlockDeclaration? = null


    override fun defaultVisit(obj: Any) {}
    private fun set(clazz: ClassDeclaration?, interfaze: InterfaceDeclaration?, fb: FunctionBlockDeclaration?) {
        this.clazz = clazz; this.interfaze = interfaze; this.functionBlock = fb
    }

    override fun visit(clazz: ClassDeclaration) {
        set(clazz, null, null)
        super.visit(clazz)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        set(null, interfaceDeclaration, null)
        super.visit(interfaceDeclaration)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        set(null, null, functionBlockDeclaration)
        super.visit(functionBlockDeclaration)
    }


    override fun visit(method: MethodDeclaration) {
        // All methods in an interface are abstract
        method.isAbstract = method.isAbstract || interfaze != null

        method.parent = get()

        //search for overrides
        if (method.isOverride) {
            val sm = getSuperMethods()
            for ((where, cand) in sm) {
                if (method sameSignature cand) {
                    method.overrides = where to cand
                    break
                }
            }
        }
    }

    private fun get(): Classifier? = when {
        clazz != null -> clazz!!
        interfaze != null -> interfaze!!
        functionBlock != null -> functionBlock!!
        else -> null
    }

    private fun getSuperMethods(): List<Pair<HasMethods, MethodDeclaration>> {
        return when {
            clazz != null -> clazz!!.declaredMethods + clazz!!.definedMethods
            interfaze != null -> interfaze!!.definedMethods
            functionBlock != null -> TODO()
            else -> listOf()
        }
    }
}
