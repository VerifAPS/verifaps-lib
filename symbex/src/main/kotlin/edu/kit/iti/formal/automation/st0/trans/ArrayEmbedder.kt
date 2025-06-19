/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.ArrayType
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.datatypes.values.VArray
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import java.math.BigInteger

/**
 * Created by weigl on 03/10/14.
 * @author Alexander Weigl
 */
class ArrayEmbedder :
    MultiCodeTransformation(),
    CodeTransformation {
    init {
        transformations += ArrayDeclarationExploder()
    }
}

class ArrayDeclarationExploder : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        val a = state.scope.variables.flatMap { explode(it) }
        state.scope.variables += a

        val records = state.scope.types.values.filter { it is RecordType }.map { it as RecordType }
        records.forEach { explode(it) }

        return state
    }

    private fun explode(vd: VariableDeclaration): List<VariableDeclaration> {
        val dt = vd.dataType
        return if (dt is ArrayType) {
            explode(vd, vd.dataType as ArrayType)
        } else {
            listOf()
        }
    }

    private fun explode(vd: VariableDeclaration, arrayType: ArrayType): List<VariableDeclaration> {
        val (dt, v) = vd.initValue as VArray
        val groundType = arrayType.fieldType
        return arrayType.allIndices().map {
            val init = v[it]
            val name = vd.name + it.joinToString("_", "_")
            val svd = VariableDeclaration(
                name,
                vd.type,
                SimpleTypeDeclaration("anonym", RefTo(groundType), null),
            )
            svd.also { svd.initValue = init }
        }
    }

    private fun explode(it: RecordType) {
        val n = it.fields.flatMap { explode(it) }
        it.fields.addAll(n)
    }
}

private fun removeArrays(fields: VariableScope) {
    fields.removeAll { it.dataType is ArrayType }
}

private class ArrayAccessRenameVisitor : AstMutableVisitor() {
    /**
     * Name of the array which isType accessed.
     */
    val toRename: String? = null

    /**
     * Index to be accessed.
     */
    val access: Int = 0

    /**
     * Subscript, i.e., the value of the index being accessed.
     */
    val subscript: Expression? = null

    override fun visit(symbolicReference: SymbolicReference): Expression {
        if (symbolicReference.identifier == toRename && symbolicReference.hasSubscripts()) {
            symbolicReference.identifier = "$toRename$$access"
            symbolicReference.subscripts = null
        } else if (subscript is SymbolicReference && symbolicReference == subscript) {
            return IntegerLit(UINT, access.toBigInteger()) // Set constant value for subscript (if it isType a symbolic reference)
        }
        return super.visit(symbolicReference)
    }
}

private class ArrayEmbedderVisitor : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(ArrayEmbedderVisitorImpl(state.scope)) as StatementList
        return state
    }

    private class ArrayEmbedderVisitorImpl(val scope: Scope) : AstMutableVisitor() {
        override fun visit(assignmentStatement: AssignmentStatement): Statement {
            if (hasArrayAccess(assignmentStatement.location as SymbolicReference)) {
                val ex = ArrayExplosion(scope, assignmentStatement.location as SymbolicReference) {
                    val a = AssignmentStatement(it, assignmentStatement.expression, assignmentStatement.reference)
                    StatementList(a)
                }
                return ex.invoke()
            }
            return super.visit(assignmentStatement)
        }

        override fun visit(symbolicReference: SymbolicReference): Expression {
            /*if (hasArrayAccess(assignmentStatement.location as SymbolicReference)) {
                val ex = ArrayExplosion(scope, assignmentStatement.location as SymbolicReference) {
                    val a = AssignmentStatement(it, assignmentStatement.expression, assignmentStatement.reference)
                    StatementList(a)
                }
                return ex.invoke()
            }*/
            return super.visit(symbolicReference)
        }
    }
}

// a[1,6].b[1] => a_1_6.b_1
// a[x].b[y] = case x of 1: case y of 1: a_1.b_1
// a[x].c.b[y].d = case x of 1: case y of 1: a_1.b_1
// a[x+1] = case x+1 of 1:  a_1
class ArrayExplosion(val s: Scope, val origRef: SymbolicReference, val end: (SymbolicReference) -> StatementList) {
    fun append(a: SymbolicReference?, b: SymbolicReference): SymbolicReference {
        fun end(c: SymbolicReference): SymbolicReference = if (c.hasSub()) end(c.sub!!) else c
        if (a != null) {
            val a = a.clone()
            end(a).sub = SymbolicReference(b.identifier)
            return a
        } else {
            return SymbolicReference(b.identifier)
        }
    }

    operator fun invoke(ref: SymbolicReference = origRef, cur: SymbolicReference? = null): StatementList {
        if (!ref.isArrayAccess) {
            val sub = ref.sub
            if (sub != null) {
                invoke(sub, append(cur, ref))
            } else {
                return if (cur != null) end(cur) else StatementList()
            }
        }
        try {
            val arrayType = (cur?.dataType(s) as ArrayType?) ?: s.resolveDataType(ref.identifier) as ArrayType
            /*val idx = ref.subscripts.foldIndexed(listOf<List<Int>>()) { n, seq, e ->
                when (e) {
                    is IntegerLit -> seq.map { it + e.value.toInt() }
                    else -> {
                        arrayType.ranges[n].toIntRange().flatMap { v ->
                            seq.map { it + n }
                        }
                    }
                }
            }*/
            val idx = ref.subscripts!!.mapIndexed { n, e ->
                when (e) {
                    is IntegerLit -> listOf(e.value.toInt())
                    else -> {
                        arrayType.ranges[n].toIntRange().toList()
                    }
                }
            }
            return foldR(ref?.sub, cur, listOf(), idx, ref.identifier, ref.subscripts!!)
        } catch (e: ClassCastException) {
            throw IllegalStateException("Array access of none array type. $origRef")
        }
    }

    private fun foldR(
        ref: SymbolicReference?,
        cur: SymbolicReference?,
        sel: List<Int>,
        idx: List<List<Int>>,
        name: String,
        elist: ExpressionList,
    ): StatementList {
        if (idx.isEmpty()) {
            val name = name + sel.joinToString("_", "_")
            val finalRef = append(cur, SymbolicReference(name))
            return if (ref != null) {
                invoke(ref, finalRef)
            } else {
                end(finalRef)
            }
        } else {
            val n = sel.size
            val case = CaseStatement(elist[n])
            case.cases =
                idx[n].map {
                    val case = Case()
                    case.addCondition(CaseCondition.IntegerCondition(IntegerLit(INT, BigInteger.valueOf(it.toLong()))))
                    case.statements = foldR(ref, cur, sel + it, idx, name, elist)
                    case
                }.toMutableList()
            return StatementList(case)
        }
    }
}

fun truncate(origRef: SymbolicReference, size: Int): SymbolicReference {
    if (size == 0) {
        val o = origRef.copy()
        o.sub = null
        o.subscripts = null
        return o
    } else {
        val r = truncate(origRef.sub!!, size - 1)
        return SymbolicReference(origRef.identifier, r)
    }
}

private fun hasArrayAccess(reference: SymbolicReference): Boolean = reference.hasSubscripts() || (reference.hasSub() && hasArrayAccess(reference.sub!!))