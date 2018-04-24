package edu.kit.iti.formal.asdl

import java.io.File
import java.io.PrintWriter
import java.io.StringWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.04.18)
 */
class SMVADSL : ADSL() {
    init {
        module {
            pkgName = "edu.kit.iti.formal.smv.ast"
            classPrefix = "Smv"
            name = "ast"

            group("Ast") {
                group("Expr") {
                    property("Position position")
                    leaf("Assignment", "Variable rhs, Expr lhs")
                    leaf("BinaryExpression", "Expr left, BinaryOperator op, Expr right")
                    leaf("CaseExpression", "Case* cases")
                    leaf("Function", "String name", "Expr* arguments")
                    group("Literal") {
                        leaf("WordLiteral", "int width, boolean signed, BigInteger value")
                        leaf("IntegerLiteral", "BigInteger value")
                        leaf("RealLiteral", "BigDecimal value")
                        leaf("BoolLiteral", "boolean value")
                        leaf("EnumLiteral", "String value")
                        leaf("EnumLiteral", "String value")
                    }
                    leaf("Quantified", "Quantifier quantifier, Expr* quantified")
                    leaf("UnaryExpression", "UnaryOperator op, Expr expr")
                    leaf("Variable", "String* names")
                }
                leaf("Module")
            }
        }
    }

    fun generate(output: File) {
        val testGenerator = TestGenerator()
        this.generate(testGenerator)
        println(testGenerator.sstream.toString())
        generate(JavaGenerator(output))
    }
}

class TestGenerator : Generator() {
    val sstream = StringWriter()
    val writer = PrintWriter(sstream)

    override fun visit(l: Leaf) {
        newline()
        writer.format("Leaf: %s.%s", l.pkgName, l.name)
        visit(l.properties)
    }

    override fun visit(g: Group) {
        newline()
        writer.format("Group: %s.%s", g.pkgName, g.name)
        visit(g.properties)
        increment()
        g.nodes.forEach { it.accept(this) }
        decrement()
    }

    private fun visit(g: Set<NodeProperty>) {
        increment()
        g.forEach {
            newline()
            writer.format("Property: %s : %s%s%s%s", it.name, it.type,
                    if (it.many) "*" else "",
                    if (it.optional) "?" else "",
                    if (it.reference) ">" else "")
        }
        decrement()
    }

    private fun newline() {
        writer.print('\n')
        (0..level).forEach {
            writer.print("\t")
        }
    }

    private var level: Int = 0

    private fun decrement() {
        level--
    }

    private fun increment() {
        level++
    }

    override fun visit(m: Module) {
        newline()
        writer.format("Module: %s.%s", m.pkgName, m.name)
        increment()
        m.nodes.forEach { it.accept(this) }
        decrement()
    }

    /*override fun visit(e: Enum) {
        newline()
        writer.format("Enum %s.%s:", e.pkgName, e.name)
    }*/
}
