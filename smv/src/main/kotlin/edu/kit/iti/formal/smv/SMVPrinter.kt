package edu.kit.iti.formal.smv

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.smv.ast.*
import org.jetbrains.annotations.NotNull
import java.io.*

class SMVPrinter(val stream: PrintWriter) : SMVAstVisitor<Unit> {
    val sort = true

    override fun visit(top: SMVAst) {
        throw IllegalArgumentException("not implemented for $top")
    }


    override fun visit(be: SBinaryExpression) {
        val pleft = precedence(be.left)
        val pright = precedence(be.right)
        val pown = precedence(be)

        if (pleft > pown) stream.print('(')
        be.left.accept(this)
        if (pleft > pown) stream.print(')')

        stream.print(" " + be.operator.symbol() + " ")

        if (pright > pown) stream.print('(')
        be.right.accept(this)
        if (pright > pown) stream.print(')')
    }

    private fun precedence(expr: SMVExpr): Int {
        if (expr is SBinaryExpression) {
            val (_, operator) = expr
            return operator.precedence()
        }
        if (expr is SUnaryExpression) {
            return expr.operator.precedence()
        }

        return if (expr is SLiteral || expr is SVariable
                || expr is SFunction) {
            -1
        } else 1000

    }

    override fun visit(ue: SUnaryExpression) {
        if (ue.expr is SBinaryExpression) {
            stream.print(ue.operator.symbol())
            stream.print("(")
            ue.expr.accept(this)
            stream.print(")")
        } else {
            stream.print(ue.operator.symbol())
            ue.expr.accept(this)
        }
    }

    override fun visit(l: SLiteral) {
        stream.print(l.dataType!!.format(l.value))
    }

    override fun visit(a: SAssignment) {
        a.target.accept(this)
        stream.print(" := ")
        a.expr.accept(this)
        stream.print(";\n")
    }

    override fun visit(ce: SCaseExpression) {
        stream.print("case \n")
        for ((condition, then) in ce.cases) {
            (condition.accept(this))
            stream.print(" : ")
            (then.accept(this))
            stream.print("; ")
        }
        stream.print("\nesac")
    }

    override fun visit(m: SMVModule) {
        stream.print("MODULE ")
        stream.print(m.name)
        if (!m.moduleParameters.isEmpty()) {
            stream.print("(");
            m.moduleParameters.forEachIndexed { index, sVariable ->
                sVariable.accept(this)
                if (index + 1 < m.moduleParameters.size) stream.print(", ")
            }
            stream.print(")")
        }
        stream.print('\n')

        printVariables("IVAR", m.inputVars)
        printVariables("FROZENVAR", m.frozenVars)
        printVariables("VAR", m.stateVars)

        printDefinition(m.definitions)

        printSection("LTLSPEC", m.ltlSpec)
        printSection("CTLSPEC", m.ctlSpec)
        printSection("INVARSPEC", m.invariantSpecs)
        printSection("INVAR", m.invariants)
        printSectionSingle("INIT", m.initExpr)
        printSectionSingle("TRANS", m.transExpr)

        if (m.initAssignments.size > 0 || m.nextAssignments.size > 0) {
            stream.print("ASSIGN\n")
            printAssignments("init", m.initAssignments)
            printAssignments("next", m.nextAssignments)
        }

        stream.print("\n-- end of module ");
        stream.print(m.name);
        stream.print('\n')
    }

    private fun printSectionSingle(section: String, exprs: List<SMVExpr>) {
        if (!exprs.isEmpty()) {
            stream.print(section)
            stream.print("\n")
            stream.print("\t")
            exprs.conjunction().accept(this)
            stream.print(";\n")
        }
    }


    private fun printDefinition(assignments: List<SAssignment>) {
        stream.printf("DEFINE\n")
        for ((target, expr) in assignments) {
            stream.print("\t")
            stream.print(target.name)
            stream.print(" := ")
            expr.accept(this)
            stream.print(";\n")
        }
    }

    private fun printAssignments(func: String, a: List<SAssignment>) {
        val assignments = if (sort) a.sortedBy { it.target.name } else a
        for ((target, expr) in assignments) {
            stream.print("\t")
            stream.print(func)
            stream.print('(')
            stream.print(target.name)
            stream.print(") := ")
            expr.accept(this)
            stream.print(";\n")
        }
    }

    private fun printSection(section: String, exprs: List<SMVExpr>) {
        if (exprs.isNotEmpty()) {
            exprs.forEach { e ->
                stream.print(section)
                stream.print("\n\t")
                e.accept(this)
                stream.print(";\n\n")
            }
        }
    }

    override fun visit(func: SFunction) {
        when (func.name) {
            SMVFacade.FUNCTION_ID_BIT_ACCESS ->
                visitBitAccess(func)
        }

        stream.print(func.name)
        stream.print('(')
        func.arguments.forEachIndexed { i, e ->
            e.accept(this)
            if (i + 1 < func.arguments.size)
                stream.print(", ")
        }
        stream.print(')')
    }

    private fun visitBitAccess(func: SFunction) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(quantified: SQuantified) {
        when (quantified.operator.arity()) {
            1 -> {
                stream.print(quantified.operator.symbol())
                stream.print("( ")
                quantified[0].accept(this)
                stream.print(")")
            }
            2 -> {
                stream.print("( ")
                (quantified[0].accept(this))
                stream.print(")")
                stream.print(quantified.operator.symbol())
                stream.print("( ")
                (quantified[1].accept(this))
                stream.print(")")
            }
            else -> throw IllegalStateException("too much arity")
        }
    }

    private fun printVariables(type: String, v: List<SVariable>) {
        val vars =
                if (sort) v.sorted()
                else v

        if (vars.isNotEmpty()) {
            stream.print(type)
            stream.print('\n')

            for (svar in vars) {
                stream.print('\t')
                stream.print(svar.name)
                stream.print(" : ")
                stream.print(svar.dataType?.repr())
                stream.print(";\n")
            }

            stream.print("-- end of ")
            stream.print(type)
            stream.print('\n')
        }
    }


    override fun visit(v: SVariable) {
        stream.print(v.name)
    }

    companion object {
        @JvmStatic
        fun toString(m: SMVAst): String {
            val w = StringWriter()
            val s = PrintWriter(w)
            val p = SMVPrinter(s)
            m.accept(p)
            s.close()
            return w.toString()
        }

        @JvmStatic
        fun toFile(m: @NotNull SMVAst, file: @NotNull File, append: Boolean = false) {
            PrintWriter(BufferedWriter(FileWriter(file, append))).use {
                val p = SMVPrinter(it)
                m.accept(p)
            }
        }
    }
}
