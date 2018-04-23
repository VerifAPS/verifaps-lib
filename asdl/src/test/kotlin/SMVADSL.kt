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
                    leaf("Quantified", "Quantifier quantifier, Expr* quantified")
                    leaf("UnaryExpression", "UnaryOperator op, Expr expr")
                    leaf("Variable", "String* names")
                }
                leaf("Module")
            }
        }
    }

    @Test
    fun test() = generate(File("tmp/smv"))

    fun generate(output: File) {
        val testGenerator = TestGenerator()
        this.generate(testGenerator)
        println(testGenerator.sstream.toString())

        val propertyToJavaString = { it: NodeProperty ->
            if (it.reference) {
                if (!it.many)
                    """
                    private IdentifierPlaceHolder<${it.type}> ${it.name} = new IdentifierPlaceHolder<>();
                    public ${it.type} get${it.name.capitalize()}() { return ${'$'}{it.name}.get();}
                    public void set${it.name.capitalize()}(${it.type} obj) { return ${it.name}.set(obj);}

                    public void set${it.name.capitalize()}Identifier(Reference obj) { ${it.name}.setName(obj);}
                    public Reference get${it.name.capitalize()}Identifier() { return ${it.name}.getName();}

                    public IdentifierPlaceHolder<${it.type}> get${it.name.capitalize()}Reference() { return ${it.name}; }
                    """
                else
                    """
                    private List<IdentifierPlaceHolder<${it.type}>> ${it.name} = new ArrayList<>();
                    /*public ${it.type} get${it.name.capitalize()}() { return ${'$'}{it.name}.get();}
                    public void set${it.name.capitalize()}(${it.type} obj) { return ${it.name}.set(obj);}

                    public void set${it.name.capitalize()}Identifier(Reference obj) { ${it.name}.setName(obj);}
                    public Reference get${it.name.capitalize()}Identifier() { return ${it.name}.getName();}

                    public IdentifierPlaceHolder<${it.type}> get${it.name.capitalize()}Reference() { return ${it.name}; }
                    */
                    """
            } else if (it.many) {
                """
                private IdentifierPlaceHolder<${it.type}> ${it.name} = new IdentifierPlaceHolder<>();
                public List<${it.type}> get${it.name.capitalize()}() { return ${it.name}.get();}

                public void add${it.name.capitalize()}(${it.name} obj) { ${it.name}.add(obj);}
                public void remove${it.name.capitalize()}(${it.name} obj) { ${it.name}.remove(obj);}
                """
            } else {
                """
                    private ${it.type} ${it.name} = null;
                    public ${it.type} get${it.name.capitalize()}() { return ${it.name};}
                    public void set${it.name.capitalize()}(${it.type} obj) { ${it.name} = obj;}
                """
            }
        }


        open class TplJavaGenerator(val outputDirectory: File, val topClass: String = "Top", val visitorBaseName: String = "Visitor") : Generator() {
            val classes0: MutableList<String> = arrayListOf()

            fun visitorCreate0(n: AbstractNode): String {
                classes0 += n.name
                return "@Override public <T> T accept($visitorBaseName<T> v){ return v.visit(this); }"
            }

            override fun visit(l: Leaf) {
                asJavaFile(l) {
                    """
                    package ${l.pkgName};

                    import lombok.*;

                    @Getter @Setter
                    public class ${l.name} ${if (l.parent != null) "extends " + l.parent!!.name else ""} {
                        ${l.properties.lines { propertyToJavaString(it) }}

                        ${childrenFunction(l)}

                        ${visitorCreate0(l)}

                        ${copyFunc(l.name, l)}
                    }
                    """.trimIndent()
                }
            }

            private fun copyFunc(name: String, l: NodeWithAttributes): String {
                return """
                    @Override
                    public $name copy() {
                        $name tmp = new $name();
                        copy(tmp);
                        return tmp;
                    }

                    @Override
                    public void copy($name other) {
                        super.copy(other);//recursive call
                        ${l.properties.lines {
                    if (it.reference || !it.isNode)
                        "other.set${it.name.capitalize()}(get${it.name.capitalize()}());"
                    else if (it.many) {
                        "get${it.name.capitalize()}.forEach(a->other.add${it.name.capitalize()}(a.copy());"
                    } else {
                        "other.set${it.name.capitalize()}(get${it.name.capitalize()}().copy());"
                    }
                }}
                    }
                    """
            }

            private fun childrenFunction(n: NodeWithAttributes): String {
                val props = n.properties.filter { !it.reference && it.isNode }.map { it.name }
                return """
                    @Override
                    public $topClass[] getChildren() {
                        $topClass[] a = $topClass[${props.size}];

                        ${if (props.isNotEmpty())
                    props.mapIndexed { index, s -> "a[$index] = $s;" }
                            .reduce { a, b -> a + "\n" + b }
                else ""}
                        return a;
                    }
                """.trimIndent()
            }


            override fun visit(l: Group) {
                traverse(l)
                asJavaFile(l) {
                    """package ${l.pkgName};
                           import lombok.*;
                           @Getter @Setters
                           public abstract class ${l.name} ${if (l.parent != null) "extends " + l.parent!!.name else ""} {
                               ${l.properties.forEach { propertyToJavaString(it) }}

                           }
                           """.trimIndent()
                }
            }

            override fun visit(m: Module) {
                traverse(m)
            }

            override fun visit(e: Enum) {
            }

            fun <T : AbstractNode> asJavaFile(n: T, func: (T) -> String) {
                val file = File(ensurePackage(n.pkgName), n.name + ".java")
                println("[asdl] $file created")
                file.bufferedWriter().use { it.write(func(n)); it.close() }
            }

            protected fun ensurePackage(pkg: String): File {
                val f = File(outputDirectory, pkg.replace('.', '/')).absoluteFile
                f.mkdirs()
                return f
            }
        }

        val visitorGen = { n: AbstractNode, p: PrintWriter ->
            p.println("""
            @Override
            public <T> T accept(Visitor<T> v) {
                return v.visit(this);
            }
            """.trimIndent())
        }
        generate(TplJavaGenerator(output))
    }
}

private fun <T> Iterable<T>.lines(function: (T) -> String): String =
        try {
            this.map { function(it) }.reduce({ a, b -> a + "\n" + b })
        } catch (e: UnsupportedOperationException) {
            ""
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
