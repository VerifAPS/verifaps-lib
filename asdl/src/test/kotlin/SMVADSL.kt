import edu.kit.iti.formal.asdl.*
import edu.kit.iti.formal.asdl.Enum
import org.junit.Test
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
                    leaf("SQuantified", "Quantifier quantifier, Expr* quantified")
                    leaf("UnaryExpression", "UnaryOperator op, Expr expr")
                    leaf("Variable", "String* names")
                }
                leaf("SMVModule")
            }
        }
    }

    @Test
    fun test() {
        val testGenerator = TestGenerator()
        this.generate(testGenerator)
        println(testGenerator.sstream.toString())
        val jg = JavaGenerator(File("tmp/smv"))

        val packageWriter: PrintFunction<AbstractNode> = { n: AbstractNode, p: PrintWriter ->
            p.format("package %s;%n%n", n.pkgName);
        }

        val imports: PrintFunction<AbstractNode> = { n: AbstractNode, p: PrintWriter ->
            p.format("import java.lang.*;%n")
            p.format("import lombok.*;\n\n")
        }

        val classDecl: PrintFunction<AbstractNode> = { n: AbstractNode, p: PrintWriter ->
            val mod = when (n) {
                is Group -> "abstract"
                else -> ""
            }

            p.format("@Getter @Setter public %s class %s ", mod, n.name)
            if (n.parent != null)
                p.format("extends %s", n.parent?.name)
            p.print(" {\n\n")
        }

        val props = { n: AbstractNode, p: PrintWriter ->
            when (n) {
                is NodeWithAttributes -> {
                    n.properties.forEach {
                        val type = if (it.reference)
                            "IdentifierPlaceHolder<${it.type}>"
                        else if (it.many)
                            "List<${it.type}>"
                        else it.type

                        p.print(if (it.optional) "@Nullable" else "@Notnull")

                        p.print("\nprivate ${type} ${it.name}")
                        if (it.many)
                            p.print(" = new ArrayList<>();")
                        else if (it.reference)
                            p.print("= new IdentifierPlaceHolder<>()")
                        else
                            p.print(" = null;")
                        p.println()
                    }
                }
            }
        }

        val visitorGen = { n: AbstractNode, p: PrintWriter ->
            p.println("""@Override public <T> T accept(Visitor<T> v) {
                {return v.visit(this);}
              """.trimIndent());
        }
        jg.genMethods += visitorGen
        generate(jg)
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

    override fun visit(e: Enum) {
        newline()
        writer.format("Enum %s.%s:", e.pkgName, e.name)
    }

}
