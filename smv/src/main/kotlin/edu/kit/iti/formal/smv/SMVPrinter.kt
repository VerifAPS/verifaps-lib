package edu.kit.iti.formal.smv

import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.CodeWriter
import org.jetbrains.annotations.NotNull
import java.io.BufferedWriter
import java.io.File
import java.io.FileWriter

class SMVPrinter(val stream: CodeWriter = CodeWriter()) : SMVAstVisitor<Unit> {
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
        stream.print(";").nl()
    }

    override fun visit(ce: SCaseExpression) {
        stream.print("case").increaseIndent()
        for ((condition, then) in ce.cases) {
            stream.nl()
            condition.accept(this)
            stream.print(" : ")
            then.accept(this)
            stream.print("; ")
        }
        stream.decreaseIndent().nl().print("esac")
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
        stream.nl()

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
            stream.print("ASSIGN").increaseIndent()
            printAssignments("init", m.initAssignments)
            printAssignments("next", m.nextAssignments)
            stream.decreaseIndent()
        }
        stream.nl().print("-- end of module ${m.name}").nl()
    }

    private fun printSectionSingle(section: String, exprs: List<SMVExpr>) {
        if (!exprs.isEmpty()) {
            stream.print(section).increaseIndent().nl()
            exprs.conjunction().accept(this)
            stream.print(";").decreaseIndent().nl()
        }
    }


    private fun printDefinition(assignments: List<SAssignment>) {
        stream.printf("DEFINE").increaseIndent()
        for ((target, expr) in assignments) {
            stream.nl().print(target.name).print(" := ")
            expr.accept(this)
            stream.print(";")
        }
        stream.decreaseIndent()
    }

    private fun printAssignments(func: String, a: List<SAssignment>) {
        val assignments = if (sort) a.sortedBy { it.target.name } else a
        for ((target, expr) in assignments) {
            stream.nl().print(func).print('(').print(target.name).print(") := ")
            expr.accept(this)
            stream.print(";")
        }
    }

    private fun printSection(section: String, exprs: List<SMVExpr>) {
        if (exprs.isNotEmpty()) {
            exprs.forEach { e ->
                stream.print(section).increaseIndent().nl()
                e.accept(this)
                stream.decreaseIndent().nl().nl()
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
            stream.print(type).increaseIndent()

            for (svar in vars) {
                stream.nl()
                printQuoted(svar.name)
                stream.print(" : ")
                stream.print(svar.dataType?.repr() ?: "<")
                stream.print(";")
            }

            stream.decreaseIndent().nl().print("-- end of $type").nl()
        }
    }


    private val RESERVED_KEYWORDS = hashSetOf("A", "E", "F", "G", "INIT", "MODULE", "case", "easc",
            "next", "init", "TRUE", "FALSE", "in", "mod", "union", "process", "AU", "EU", "U", "V", "S",
            "T", "EG", "EX", "EF", "AG", "AX", "AF", "X", "Y", "Z", "H", "O", "min", "max")

    override fun visit(v: SVariable) = printQuoted(v.name)

    fun printQuoted(name: String) {
        if (name in RESERVED_KEYWORDS)
            stream.print("\"$name\"")
        else
            stream.print(name)
    }

    companion object {
        @JvmStatic
        fun toString(m: SMVAst): String {
            val s = CodeWriter()
            val p = SMVPrinter(s)
            m.accept(p)
            return s.stream.toString()
        }

        @JvmStatic
        fun toFile(m: @NotNull SMVAst, file: @NotNull File, append: Boolean = false) {
            BufferedWriter(FileWriter(file, append)).use { stream ->
                CodeWriter(stream).let {
                    val p = SMVPrinter(it)
                    m.accept(p)
                }
            }
        }
    }
}
