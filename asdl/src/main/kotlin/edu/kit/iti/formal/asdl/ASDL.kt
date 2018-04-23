package edu.kit.iti.formal.asdl

import java.io.File
import java.io.PrintWriter


abstract class AbstractNode {
    var name: String = ""
    var pkgName: String = ""
    var parent: AbstractNode? = null
    var skip: Boolean = false

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
        g.name = name
        f(g)
        return group(g)
    }


    fun leaf(name: String): Leaf {
        val l = Leaf()
        l.name = name
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

interface HasAspects<T> {
    val aspects: MutableList<Aspect<T>>
}

class Enum : AbstractNode() {
    override fun <T> accept(visitor: Visitor<T>): T = visitor.visit(this)
}

class Group : NodeWithAttributes, NodeContainer, AbstractNode(), HasAspects<Group> {
    override val aspects: MutableList<Aspect<Group>> = arrayListOf()
    override val nodes: MutableList<AbstractNode> = arrayListOf()
    override val properties: MutableSet<NodeProperty> = mutableSetOf()
    override fun <T> accept(visitor: Visitor<T>) = visitor.visit(this)
}

class Leaf : NodeWithAttributes, HasAspects<Leaf>, AbstractNode() {
    override val aspects: MutableList<Aspect<Leaf>> = arrayListOf()
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
                        var reference: Boolean = false,
                        var isNode: Boolean = true) {
    init {
        type = type.trim('*', '?', '>')
    }

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
            it.accept(ParentSetter())
            setIsNodeType(it)
            it.accept(ClassPrefixPropagation())
            it.accept(generator)
        }
    }
}

class ParentSetter() : Traversal<Unit>() {

    override fun visit(l: Leaf) {
        l.parent = parent;
    }

    override fun visit(g: Group) {
        g.parent = parent
        parent = g
        traverse(g)
        parent = g.parent
    }

    override fun visit(m: Module) {
        traverse(m)
    }

    override fun visit(e: Enum) {
        e.parent = parent
    }

    var parent: AbstractNode? = null
}

fun setIsNodeType(m: Module) {
    val names = mutableSetOf<String>()
    val props = arrayListOf<NodeProperty>()
    val prefix = m.classPrefix

    class GetNodes : Traversal<Unit>() {
        override fun visit(l: Leaf) {
            names.add(l.name)
            names.add(prefix + l.name)
            props.addAll(l.properties)
        }

        override fun visit(l: Group) {
            names.add(l.name)
            names.add(prefix + l.name)
            props.addAll(l.properties)
            traverse(l)
        }

        override fun visit(m: Module) {
            traverse(m)
        }

        override fun visit(e: Enum) {}
    }

    m.accept(GetNodes())
    println(names)
    props.forEach { it.isNode = it.type in names }
}


/**
 *
 */
class ClassPrefixPropagation : Traversal<Unit>() {
    lateinit var prefix: String
    override fun visit(l: Leaf) {
        l.name = prefixed(l.name)
        l.properties.forEach { visit(it) }
    }

    private fun visit(it: NodeProperty) {
        if (it.isNode)
            it.type = prefixed(it.type)
    }

    private fun prefixed(name: String): String =
            if (name.startsWith(prefix))
                name else prefix + name

    override fun visit(g: Group) {
        g.name = prefixed(g.name)
        g.properties.forEach { visit(it) }
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

/**
 *
 */
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

abstract class Generator : Traversal<Unit>()

typealias PrintFunction<T> = (T, PrintWriter) -> Unit

interface Aspect<T> {
    fun imports(obj: T, p: PrintWriter) = Unit
    fun beforeClassDecl(obj: T, p: PrintWriter) = Unit
    fun properties(obj: T, p: PrintWriter) = Unit
    fun members(obj: T, p: PrintWriter) = Unit
    fun endOfClass(obj: T, p: PrintWriter) = Unit
    fun afterClass(obj: T, p: PrintWriter) = Unit
}

open class JavaGenerator(val outputDirectory: File) : Generator() {
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

    override fun visit(e: Enum) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

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
