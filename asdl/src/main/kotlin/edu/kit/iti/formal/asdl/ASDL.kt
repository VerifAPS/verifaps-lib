package edu.kit.iti.formal.asdl

<<<<<<< HEAD
import java.io.File


abstract class AbstractNode {
    var name: String = ""
    var pkgName: String = ""
=======

abstract class AbstractNode {
    var name: String=""
    var pkgName: String=""
>>>>>>> fd2d040... wip

    abstract fun <T> accept(visitor: Visitor<T>): T
}

interface NodeContainer {
    val nodes: MutableList<AbstractNode>

    fun group(name: String): Group {
        val l = Group()
        l.name
        return group(l)
    }

    fun group(group: Group): Group {
        nodes.add(group)
        return group
    }

    fun group(name: String, f: Group.() -> Unit): Group {
        val g = Group()
<<<<<<< HEAD
        g.name = name
=======
>>>>>>> fd2d040... wip
        f(g)
        return group(g)
    }


    fun leaf(name: String): Leaf {
        val l = Leaf()
<<<<<<< HEAD
        l.name = name
=======
        l.name
>>>>>>> fd2d040... wip
        return leaf(l)
    }

    fun leaf(name: Leaf): Leaf {
        nodes.add(name)
        return name
    }

    fun leaf(name: String, init: Leaf.() -> Unit): Leaf {
        val n = leaf(name)
        init(n)
        return n
    }

    fun leaf(name: String, props: String): NodeWithAttributes {
        return leaf(name, *props.split(", ").toTypedArray())
    }

    fun leaf(name: String, vararg props: String): Leaf {
        val args = props.map {
            NodeProperty.translate(it)
        }
        return leaf(name, *args.toTypedArray())
    }

    fun leaf(name: String, vararg props: NodeProperty): Leaf {
        val n = leaf(name)
        props.forEach { n.property(it) }
        return n
    }
}

interface NodeWithAttributes {
    val properties: MutableSet<NodeProperty>

    fun optional(clazz: Class<*>, name: String): NodeProperty = property(clazz.name, name, optional = true)
    fun optional(type: String, name: String) = property(type, name, optional = true)
    fun many(clazz: Class<*>, name: String) = property(clazz.name, name, many = true)
    fun many(type: String, name: String): NodeProperty = property(type, name, many = true)

    fun property(p: NodeProperty): NodeProperty {
        properties.add(p)
        return p
    }

    fun property(type: String, name: String, optional: Boolean = false, many: Boolean = false, reference: Boolean = false): NodeProperty {
        val n = NodeProperty(name, type, optional, many, reference)
        return property(n)
    }

    fun property(f: NodeProperty.() -> Unit): NodeProperty {
        val n = NodeProperty()
        f(n)
        return property(n)
    }

    fun property(def: String): NodeProperty {
        return property(NodeProperty.translate(def))
    }
}

class Enum : AbstractNode() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

class Group : NodeWithAttributes, NodeContainer, AbstractNode() {
    override val nodes: MutableList<AbstractNode> = arrayListOf()
    override val properties: MutableSet<NodeProperty> = mutableSetOf()
    override fun <T> accept(visitor: Visitor<T>) = visitor.visit(this)
}

class Leaf : NodeWithAttributes, AbstractNode() {
    override val properties: MutableSet<NodeProperty> = hashSetOf()
    override fun <T> accept(visitor: Visitor<T>) = visitor.visit(this)
}

class Module : NodeContainer, AbstractNode() {
    override val nodes: MutableList<AbstractNode> = arrayListOf()
    var classPrefix: String = ""
    override fun <T> accept(visitor: Visitor<T>) = visitor.visit(this)
}

data class NodeProperty(var name: String = "",
                        var type: String = "",
                        var optional: Boolean = false,
                        var many: Boolean = false,
                        var reference: Boolean = false) {
<<<<<<< HEAD

    init {
        type = type.trim('*', '?', '>')
    }

=======
>>>>>>> fd2d040... wip
    companion object {
        internal fun translate(type: String): NodeProperty {
            try {
                val (t, n) = type.split(" ")
                if (t.endsWith("*"))
                    return NodeProperty(n, t, many = true)
                else
                    if (t.trim().endsWith("?")) {
                        return NodeProperty(n, t, optional = true)
                    } else {
                        return NodeProperty(n, t)
                    }
            } catch (e: IndexOutOfBoundsException) {
                println(type)
                throw e
            }
        }
    }

}

interface Visitor<out T> {
    fun visit(l: Leaf): T
    fun visit(g: Group): T
    fun visit(m: Module): T
    fun visit(e: Enum): T
}

abstract class Traversal<T> : Visitor<T> {
    fun traverse(l: Leaf) {}
    fun traverse(g: Group) {
        g.nodes.forEach { it.accept(this) }
    }

    fun traverse(m: Module) {
        m.nodes.forEach { it.accept(this) }
    }

    fun traverse(e: Enum) {}
}


open class ADSL {
    var modules = arrayListOf<Module>()
    fun module(init: Module.() -> Unit): Module {
        val m = Module()
        init(m)
        modules.add(m)
        return m
    }

    fun generate(generator: Generator) {
        modules.forEach {
            it.accept(PackagePropagation())
            it.accept(ClassPrefixPropagation())
            it.accept(generator)
        }
    }
}

class ClassPrefixPropagation : Traversal<Unit>() {
    lateinit var prefix: String
    override fun visit(l: Leaf) {
        if (!l.name.startsWith(prefix))
            l.name = prefix + l.name
    }

    override fun visit(g: Group) {
        if (!g.name.startsWith(prefix))
            g.name = prefix + g.name
        traverse(g)
    }

    override fun visit(m: Module) {
        prefix = m.classPrefix
        traverse(m)
    }

    override fun visit(e: Enum) {
        if (!e.name.startsWith(prefix))
            e.name = prefix + e.name
    }
}

class PackagePropagation : Traversal<Unit>() {
    lateinit var currentPackage: String

    override fun visit(l: Leaf) {
        if (l.pkgName.isBlank())
            l.pkgName = currentPackage
    }

    override fun visit(g: Group) {
        if (g.pkgName.isBlank())
            g.pkgName = currentPackage

        val old = currentPackage
        currentPackage = g.pkgName
        traverse(g)
        currentPackage = old
    }

    override fun visit(m: Module) {
        currentPackage = m.pkgName
        traverse(m)
    }

    override fun visit(e: Enum) {
        if (e.pkgName.isBlank())
            e.pkgName = currentPackage
    }
}

abstract class Generator : Visitor<Unit>

class JavaGenerator(val outputDirectory: File,
                    val memberGeneratorsGroup : List<(Leaf) -> String> = arrayListOf(),
                    val memberGeneratorsLeaf : List<(Leaf) -> String> = arrayListOf()) : Generator() {

    protected fun ensurePackage(pkg: String): File {
        val f = File(outputDirectory, pkg)
        f.mkdirs()
        return f
    }

    override fun visit(l: Leaf) {
        val f = File(ensurePackage(l.pkgName), l.name)
        f.createNewFile()
        f.bufferedWriter().use {
            it.write("""
                package %s


            """.trimIndent())

        }
    }

    override fun visit(g: Group) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(m: Module) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(e: Enum) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

abstract class Generator : Visitor<Unit> {

}

class KotlinGenerator : Generator() {
    override fun visit(l: Leaf) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(g: Group) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(m: Module) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(e: Enum) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}
