package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.VOID
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * Search and set the data type attributes based on the given global scope.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 25.11.16
 */
class ResolveDataTypes(val globalScope: Scope) : AstVisitorWithScope<Unit>() {
    init {
        scope = globalScope
    }

    override fun defaultVisit(obj: Any) {
        when (obj) {
            is TypeDeclaration -> obj.initialization?.accept(this)
        }

    }

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
            vd.accept(this)
        }
    }

    /*
    override fun visit(init : IdentifierInitializer) {

    }*/

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
        return super.visit(arrayTypeDeclaration)
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        ignoreDataTypeNotDefined {
            simpleTypeDeclaration.baseType.resolve(scope::resolveDataType)
        }
        super.visit(simpleTypeDeclaration)
    }

    override fun visit(ref: SymbolicReference) {
        val first = ref.identifier
        try {
            //val dataType = scope.resolveDataType(first)
            //val et = dataType as EnumerateType?
            //ref.dataType = et
            /*if (ref.sub != null) {
                val second = (ref.sub as SymbolicReference).identifier
                // TODO...?
            }*/
        } catch (e: ClassCastException) {

        } catch (e: DataTypeNotDefinedException) {
        }
    }

    override fun visit(literal: Literal) {
        try {
            when (literal) {
                is IntegerLit -> {
                    literal.dataType.resolve(scope::resolveDataType0)
                    if (!literal.dataType.isIdentified)
                        literal.dataType.obj = INT
                }
                is RealLit -> literal.dataType.resolve(scope::resolveDataType0)
                is EnumLit -> {
                    literal.dataType.resolve(scope::resolveDataType0)
                    if (!literal.dataType.isIdentified) {
                        literal.dataType.obj = scope.resolveEnumByValue(literal.value)
                    }
                }
                is StringLit -> literal.dataType.resolve(scope::resolveDataType0)
                is BitLit -> literal.dataType.resolve(scope::resolveDataType0)
            }
        } catch (e: ClassCastException) {
        }
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        structureTypeDeclaration.fields.forEach { it.accept(this) }
    }

    override fun visit(it: VariableDeclaration) {
        //super.visit(it)
        it.typeDeclaration?.accept(this)
        ignoreDataTypeNotDefined { it.dataType = it.typeDeclaration?.getDataType(scope) }
    }

    override fun visit(invocation: InvocationStatement) {
        invocation.invoked = scope.resolveInvocation(invocation.callee)
    }

    override fun visit(invocation: Invocation) {
        super.visit(invocation)
    }

    private fun ignoreDataTypeNotDefined(func: () -> Unit) {
        try {
            func()
        } catch (e: DataTypeNotDefinedException) {

        }
    }
}

class MaintainInitialValues : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}
    override fun visit(vd: VariableDeclaration) {
        if (vd.initValue != null) return
        vd.initValue = vd.init?.getValue()
        if (vd.initValue == null && vd.dataType != null && vd.dataType != VOID) {
            vd.initValue = DefaultInitValue.getInit(vd.dataType!!)
        }
    }

}
