package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.Bits
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.scope.LocalScope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*

class State : HashMap<String, Value<*, *>>()

object defaultValues : DefaultDataTypeVisitor<Value<*, *>>() {
    override fun visit(real: AnyReal?) = Values.VAnyReal(real!!, BigDecimal.ZERO)
    override fun visit(bool: AnyBit.Bool) = Values.VBool(bool, false)
    override fun visit(anyBit: AnyBit) = Values.VAnyBit(anyBit, Bits(0, anyBit.bitLength.toLong()))
    override fun visit(anyInt: AnyInt) = Values.VAnyInt(anyInt, BigInteger.ZERO)
    override fun visit(enumerateType: EnumerateType) =
            Values.VAnyEnum(enumerateType, enumerateType.defValue)

    override fun visit(timeType: TimeType) = null
    override fun visit(string: IECString.String?) =
            Values.VIECString(string, "")

    override fun visit(wString: IECString.WString?) = Values.VIECString(wString, "")

    override fun visit(classDataType: ClassDataType): Value<*, *> {
        var map: State = StateInitializer.getState(classDataType.clazz)
        return Values.VClass(classDataType, map)
    }

}

class StateInitializer : DefaultVisitor<State>() {
    companion object {
        fun getState(decl: TopLevelScopeElement<*>): State {
            val s = StateInitializer()
            return decl.accept(s)
        }
    }

    override fun visit(programDeclaration: ProgramDeclaration?): State {
        return transform(programDeclaration!!.localScope)
    }

    private fun transform(localScope: LocalScope): State {
        val s = State()
        val ev = ExpressionEval(s)

        for ((name, vd) in localScope.localVariables) {
      //      s[vd.name] =
                    if (vd.init !== null)
                        ev.eval(vd.init!!)
                    else
                        vd.dataType.accept(defaultValues)
        }
        return s
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration?): State {
        return transform(functionBlockDeclaration!!.localScope!!)
    }

    override fun visit(fd: FunctionDeclaration): State {
        val state = transform(fd.localScope)
        //state.put(fd.functionName, fd.returnType.accept(defaultValues))
        return state
    }

    override fun visit(clazz: ClassDeclaration?): State {
        return transform(clazz!!.localScope)
    }

    override fun visit(method: MethodDeclaration?): State {
        return transform(method!!.localScope)
    }
}

class StatementEval(var state: State = State())
    : DefaultVisitor<Unit>() {

    fun eval(stmts: StatementList): State {
        stmts.accept(this)
        return state
    }

    fun eval(block: ProgramDeclaration): State {
        //TODO create state
        return eval(block.programBody)
    }

    override fun visit(caseStatement: CaseStatement?) {
        super.visit(caseStatement)
    }

    override fun visit(statements: StatementList?) {
        super.visit(statements)
    }

    override fun visit(programDeclaration: ProgramDeclaration?) {
        super.visit(programDeclaration)
    }

    override fun visit(expressions: ExpressionList?) {
        super.visit(expressions)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration?) {
        super.visit(functionBlockDeclaration)
    }

    override fun visit(returnStatement: ReturnStatement?) {
        super.visit(returnStatement)
    }

    override fun visit(ifStatement: IfStatement?) {
        super.visit(ifStatement)
    }

    override fun visit(guardedStatement: GuardedStatement?) {
        super.visit(guardedStatement)
    }

    override fun visit(fbc: FunctionBlockCallStatement?) {
        super.visit(fbc)
    }

    override fun visit(aCase: CaseStatement.Case?) {
        super.visit(aCase)
    }

    override fun visit(forStatement: ForStatement?) {
        super.visit(forStatement)
    }
}