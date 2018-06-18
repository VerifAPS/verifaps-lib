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
class ResolveDataTypes : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {}

    /**
     * {@inheritDoc}
     */
    override fun visit(functionDeclaration: FunctionDeclaration) {
        super.visit(functionDeclaration)
        functionDeclaration.returnType.resolve(scope::resolveDataType)

    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        return super.visit(functionBlockDeclaration)
    }

    override fun visit(localScope: Scope) {
        scope = localScope
        scope.variables.forEach { vd ->
            if (vd.dataType == null)
                vd.dataType = vd.typeDeclaration?.getDataType(localScope)
            if (vd.initValue == null) {
                vd.initValue = vd.init?.getValue()
            }
        }
    }


    override fun visit(classDeclaration: ClassDeclaration) {
        if (classDeclaration.parent.identifier != null) {
            classDeclaration.parent.resolve(scope::resolveClass)
            //assert(classDeclaration.parentClass != null)
        }
        val seq = classDeclaration.interfaces
        seq.forEach { it.resolve(scope::resolveInterface) }
        return super.visit(classDeclaration)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        val seq = interfaceDeclaration.interfaces
        seq.forEach { it.resolve(scope::resolveInterface) }
        return super.visit(interfaceDeclaration)
    }

    override fun visit(methodDeclaration: MethodDeclaration) {
        super.visit(methodDeclaration)
        methodDeclaration.returnType.resolve(scope::resolveDataType)

    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration) {
        return super.visit(gvlDecl)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {
        arrayTypeDeclaration.baseType.resolve(scope::resolveDataType)
        return super.visit(arrayTypeDeclaration)
    }

    override fun visit(ref: SymbolicReference) {
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


    }

    override fun visit(literal: Literal) {
        try {
            literal.dataType.resolve(scope::resolveDataType)
        } catch (e: ClassCastException) {
        } catch (e: DataTypeNotDefinedException) {
        }
    }
}
