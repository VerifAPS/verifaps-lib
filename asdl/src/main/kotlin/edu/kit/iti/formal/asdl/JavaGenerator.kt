package edu.kit.iti.formal.asdl

import java.io.File
import java.io.PrintWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (24.04.18)
 */
open class JavaGenerator(val outputDirectory: File, val topClass: String = "Top", val visitorBaseName: String = "Visitor")
    : Generator() {
    fun referenceProperty(it: NodeProperty) =
            """
                    private IdentifierPlaceHolder<${it.type}> ${it.name} = new IdentifierPlaceHolder<>();
                    public ${it.type} get${it.name.capitalize()}() { return ${'$'}{it.name}.get();}
                    public void set${it.name.capitalize()}(${it.type} obj) { return ${it.name}.set(obj);}

                    public void set${it.name.capitalize()}Identifier(Reference obj) { ${it.name}.setName(obj);}
                    public Reference get${it.name.capitalize()}Identifier() { return ${it.name}.getName();}

                    public IdentifierPlaceHolder<${it.type}> get${it.name.capitalize()}Reference() { return ${it.name}; }
                    """


    private fun referenceManyProperty(it: NodeProperty) =
            """
                    private List<IdentifierPlaceHolder<${it.type}>> ${it.name} = new ArrayList<>();
                    /*public ${it.type} get${it.name.capitalize()}() { return ${'$'}{it.name}.get();}
                    public void set${it.name.capitalize()}(${it.type} obj) { return ${it.name}.set(obj);}

                    public void set${it.name.capitalize()}Identifier(Reference obj) { ${it.name}.setName(obj);}
                    public Reference get${it.name.capitalize()}Identifier() { return ${it.name}.getName();}

                    public IdentifierPlaceHolder<${it.type}> get${it.name.capitalize()}Reference() { return ${it.name}; }
                    */
                    """.trimMargin()

    fun manyProperty(it: NodeProperty) = """
                private IdentifierPlaceHolder<${it.type}> ${it.name} = new IdentifierPlaceHolder<>();
                public List<${it.type}> get${it.name.capitalize()}() { return ${it.name}.get();}

                public void add${it.name.capitalize()}(${it.name} obj) { ${it.name}.add(obj);}
                public void remove${it.name.capitalize()}(${it.name} obj) { ${it.name}.remove(obj);}
                """

    fun simpleProperty(it: NodeProperty) = """
                    private ${it.type} ${it.name} = null;
                    public ${it.type} get${it.name.capitalize()}() { return ${it.name};}
                    public void set${it.name.capitalize()}(${it.type} obj) { ${it.name} = obj;}
                """.trimIndent()

    fun propertyToJavaString(it: NodeProperty) =
            if (it.reference) {
                if (!it.many)
                    referenceProperty(it)
                else
                    referenceManyProperty(it)
            } else if (it.many) {
                manyProperty(it)
            } else {
                simpleProperty(it)
            }

    protected val acceptableClasses: MutableList<String> = arrayListOf()

    fun visitorCreate0(n: AbstractNode): String {
        acceptableClasses += n.name
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
            """
               package ${l.pkgName};
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

    val visitorGen = { n: AbstractNode, p: PrintWriter ->
        p.println("""
            @Override
            public <T> T accept(Visitor<T> v) {
                return v.visit(this);
            }
            """.trimIndent())
    }
}

/*------------------------------------------------------------------------------------*/


open class JavaGeneratorAspect(val outputDirectory: File) : Generator() {
    val nodeAspects = arrayListOf<Aspect<AbstractNode>>()
    val leafAspects = arrayListOf<Aspect<Leaf>>()
    val groupAspects = arrayListOf<Aspect<Group>>()
    val moduleAspects = arrayListOf<Aspect<Group>>()

    open protected fun ensurePackage(pkg: String): File {
        val f = File(outputDirectory, pkg.replace('.', '/')).absoluteFile
        f.mkdirs()
        return f
    }

    open protected fun <T : AbstractNode> visit(l: T, vararg lloa: ArrayList<Aspect<T>>) {
        val f = File(ensurePackage(l.pkgName), l.name + ".java")
        f.createNewFile()
        println("$f created!")

        val _lloa = lloa.toMutableList()
        when (l) {
            is HasAspects<*> -> _lloa.add(l.aspects as ArrayList<Aspect<T>>)
        }

        f.bufferedWriter().use {
            val pw = PrintWriter(it)
            this.r(l, _lloa, pw, Aspect<T>::afterClass)
            pw.close()
        }
    }

    open protected fun <T> r(l: T, lloa: MutableList<ArrayList<Aspect<T>>>,
                             writer: PrintWriter,
                             func: (Aspect<T>, T, PrintWriter) -> Unit) {
        for (loa in lloa) {
            for (aspect in loa) {
                func.invoke(aspect, l, writer)
            }
        }
    }

    override fun visit(l: Leaf) {
        visit(l as AbstractNode)
    }

    override fun visit(g: Group) {
        visit(g as AbstractNode)
        traverse(g)
    }

    override fun visit(m: Module) {
        traverse(m)
    }
}


/*------------------------------------------------------------------------------------*/
private fun <T> Iterable<T>.lines(function: (T) -> String): String =
        try {
            this.map { function(it) }.reduce({ a, b -> a + "\n" + b })
        } catch (e: UnsupportedOperationException) {
            ""
        }
