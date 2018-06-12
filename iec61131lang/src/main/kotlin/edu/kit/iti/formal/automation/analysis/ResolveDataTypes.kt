package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * Search and set the data type attributes based on the given global scope.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 25.11.16
 */
class ResolveDataTypes : AstVisitorWithScope<Any>() {
    override fun visit(programDeclaration: ProgramDeclaration): Any? {
        super.visit(programDeclaration)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionDeclaration: FunctionDeclaration): Any? {
        super.visit(functionDeclaration)
        functionDeclaration.returnType.resolve(scope::resolveDataType)
        return null
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Any? {
        return super.visit(functionBlockDeclaration)
    }

    override fun visit(localScope: Scope): Any? {
        scope = localScope
        scope.variables.forEach { vd ->
            vd.dataType.resolve(scope::resolveDataType)
            if (vd.init != null) {
                vd.init!!.accept(this)
            }
        }
        return null
    }


    override fun visit(classDeclaration: ClassDeclaration): Any? {
        if (classDeclaration.parent.identifier != null) {
            classDeclaration.parent.resolve(scope::resolveClass)
            //assert(classDeclaration.parentClass != null)
        }
        val seq = classDeclaration.interfaces
        seq.forEach { it.resolve(scope::resolveInterface) }
        return super.visit(classDeclaration)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): Any? {
        val seq = interfaceDeclaration.interfaces
        seq.forEach { it.resolve(scope::resolveInterface) }
        return super.visit(interfaceDeclaration)
    }

    override fun visit(methodDeclaration: MethodDeclaration): Any? {
        super.visit(methodDeclaration)
        methodDeclaration.returnType.resolve(scope::resolveDataType)
        return null
    }

    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): Any? {
        return super.visit(globalVariableListDeclaration)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): Any? {
        arrayTypeDeclaration.baseType.resolve(scope::resolveDataType)
        return super.visit(arrayTypeDeclaration)
    }

    override fun visit(ref: SymbolicReference): Any? {
        val first = ref.identifier
        try {
            val dataType = scope.resolveDataType(first)
            val et = dataType as EnumerateType?
            ref.dataType = et
            if (ref.sub != null) {
                val second = (ref.sub as SymbolicReference).identifier
                // TODO...?
            }
        } catch (e: ClassCastException) {

        } catch (e: DataTypeNotDefinedException) {
        }

        return null
    }

    override fun visit(literal: Literal): Any? {
        try {
            literal.dataType.resolve(scope::resolveDataType)
        } catch (e: ClassCastException) {
        } catch (e: DataTypeNotDefinedException) {
        }

        return null
    }

}
