package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.MultiDimArrayValue
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.st.ast.*
import java.util.*

/**
 * Computes the "unfolded" state of an PLC program or given scopes.
 * @author Alexander Weigl
 * @version 1 (12.11.19)
 */
class UnfoldState {
    val state = TreeMap<String, Value<*, *>>()
    val decls = TreeMap<String, VariableDeclaration>()

    fun addPous(pous: PouElements) {
        pous.filterIsInstance<GlobalVariableListDeclaration>().forEach {
            addScope(it.scope.variables, "")
        }
        pous.filterIsInstance<ProgramDeclaration>().forEach { addScope(it.scope.variables, it.name) }
    }

    fun addScope(scope: VariableScope, prefix: String = "") {
        scope.forEach { declare(prefix, it) }
    }

    private fun declare(prefix: String, vd: VariableDeclaration) {
        val p = if (prefix.isBlank()) "" else "$prefix."
        val s = "$p${vd.name}"
        decls[s] = vd
        declare(s, vd.initValue!!)
    }

    fun declare(name: String, value: Value<*, *>) {
        value.dataType.accept(
                object : DataTypeVisitorNN<Unit> {
                    override fun defaultVisit(obj: Any) {
                        state[name] = value
                    }

                    override fun visit(arrayType: ArrayType) {
                        val arrayValue = value.value as MultiDimArrayValue
                        for (idx in arrayType.allIndices()) {
                            val n = idx.joinToString(",", "$name[", "]")
                            val v = arrayValue[idx]
                            declare(n, v)
                            decls[n] = VariableDeclaration().also { it.dataType = value.dataType; it.initValue = v }
                        }
                    }

                    override fun visit(recordType: RecordType) {
                        for (idx in recordType.fields) {
                            addScope(recordType.fields, name)
                        }
                    }


                    override fun visit(classDataType: ClassDataType) {
                        if (classDataType is ClassDataType.ClassDt) {
                            addScope(classDataType.clazz.effectiveVariables, name)
                        }
                    }

                    override fun visit(functionBlockDataType: FunctionBlockDataType) {
                        addScope(functionBlockDataType.functionBlock.effectiveVariables, name)
                    }
                })
    }
}

fun UnfoldState.classInstances() : Map<String, VariableDeclaration> {
    return decls
}

