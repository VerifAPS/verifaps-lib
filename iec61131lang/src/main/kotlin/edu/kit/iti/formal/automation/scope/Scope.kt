package edu.kit.iti.formal.automation.scope

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.st.Cloneable
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.LookupList
import edu.kit.iti.formal.automation.st.LookupListFactory
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.automation.visitors.Visitor
import java.util.*
import java.util.function.Supplier
import java.util.stream.Stream
import kotlin.collections.ArrayList

/**
 * @author Alexander Weigl
 * @version 1 (13.06.14)
 */
class Scope() : Visitable, Iterable<VariableDeclaration>, Cloneable<Scope> {
    override fun iterator(): Iterator<VariableDeclaration> = variables.iterator()

    private val allowedEnumValues = HashMap<String, EnumerateType>()

    var parent: Scope? = null
        set(parent) {
            if (parent != null) {
                programs.parent = Supplier { parent.programs }
                functionBlocks.parent = Supplier { parent.functionBlocks }
                functions.parent = Supplier { parent.functions }
                actions.parent = Supplier { parent.actions }
                classes.parent = Supplier { parent.classes }
                dataTypes.parent = Supplier<Namespace<TypeDeclaration>> { parent.dataTypes }
                interfaces.parent = Supplier { parent.interfaces }
            } else {
                programs.parent = null
                functionBlocks.parent = null
                functions.parent = null
                actions.parent = null
                classes.parent = null
                dataTypes.parent = null
                interfaces.parent = null
            }
            field = parent
        }

    var programs = Namespace<ProgramDeclaration>()
    var functionBlocks = Namespace<FunctionBlockDeclaration>()
    var functions = Namespace<FunctionDeclaration>()
    var dataTypes = Namespace<TypeDeclaration>()
    var functionResolvers: MutableList<FunctionResolver> = LinkedList()
    var types = TypeScope.builtin()
    var classes = Namespace<ClassDeclaration>()
    var interfaces = Namespace<InterfaceDeclaration>()
    val variables: VariableScope = LookupListFactory.create()
    val actions: Namespace<ActionDeclaration> = Namespace()
    val methods: Namespace<MethodDeclaration> = Namespace()


    val topLevel: Scope
        get() {
            var s: Scope? = this
            while (s!!.parent != null) s = s.parent
            return s
        }

    constructor(parent: Scope?) : this() {
        this.parent = parent
    }

    constructor(variables: List<VariableDeclaration>) : this() {
        variables.forEach { this.add(it) }
    }

    fun asMap(): VariableScope {
        return variables
    }

    fun add(vardecl: VariableDeclaration) = variables.add(vardecl)

    /**
     * {@inheritDoc}
     */
    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    fun prefixNames(s: String): Scope {
        val copy = Scope()
        for (value in variables) {
            val nd = value.clone()
            nd.name = s + nd.name
            copy.add(nd)
        }
        return copy
    }

    /**
     * {@inheritDoc}
     *
    override fun toString(): String {
        val sb = StringBuilder("Scope{")
        for (vd in variables) {
            sb.append(vd.name).append(":").append(vd.dataType)
            if (vd.init != null) sb.append(" := ").append(vd.init)
            sb.append("},")
        }
        sb.delete(sb.length - 1, sb.length)
        sb.append("}")
        return sb.toString()
    }*/

    @Throws(VariableNotDefinedException::class)
    fun getVariable(reference: SymbolicReference): VariableDeclaration {
        if (reference.identifier in variables)
            return (variables[reference.identifier] as VariableDeclaration?)!!
        throw VariableNotDefinedException(this, reference)
    }

    @Throws(VariableNotDefinedException::class)
    fun getVariable(s: String): VariableDeclaration? {
        if (s in variables) {
            return variables[s]
        }
        return if (this.parent != null) this.parent!!.getVariable(s)
        else throw VariableNotDefinedException(this, s)
    }


    fun builder(): VariableBuilder {
        return VariableBuilder(variables)
    }

    fun filterByFlags(flags: Int): List<VariableDeclaration> {
        return variables.filter { it.isType(flags) }
    }

    fun hasVariable(variable: String): Boolean {
        return variable in variables || this.parent != null && this.parent!!.hasVariable(variable)
    }

    fun resolveProgram(key: String) = programs.lookup(key)
    fun resolveFunctionBlock(key: String) = functionBlocks.lookup(key)
    fun resolveFunction(key: String) = functions.lookup(key)
    fun registerProgram(programDeclaration: ProgramDeclaration) = programs.register(programDeclaration.name!!, programDeclaration)
    fun registerFunction(functionDeclaration: FunctionDeclaration) = functions.register(functionDeclaration.name, functionDeclaration)


    fun registerFunctionBlock(fblock: FunctionBlockDeclaration) = functionBlocks.register(fblock.name, fblock)

    fun registerType(dt: TypeDeclaration) {
        dataTypes.register(dt.name, dt)
        if (dt is EnumerationTypeDeclaration) {
            val edt = dt.getDataType(this)
            dt.allowedValues
                    .map { it.text!! }
                    .forEach { allowedEnumValues[it] = edt }
        }
    }


    fun resolveDataType(name: String): AnyDt? {
        if (types.containsKey(name))
            return types[name]

        val a = functionBlocks.containsKey(name)
        val b = dataTypes.containsKey(name)
        val c = classes.containsKey(name)
        val d = interfaces.containsKey(name)

        //if (a && b || a && c || b && c) {
        if (a && b || b && c) {
            System.err.println("Ambiguity in Name Resolution for: $name")
        }

        val q: AnyDt?
        if (a) {
            q = FunctionBlockDataType(functionBlocks.lookup(name)!!)
            types[name] = q
            return q
        }

        if (b) {
            q = dataTypes.lookup(name)!!.getDataType(this)!!
            types[name] = q
            return q
        }

        if (c) {
            val cd = classes.lookup(name)!!
            q = ClassDataType(cd)
            types[name] = q
            return q
        }

        if (d) {
            q = InterfaceDataType(interfaces.lookup(name)!!)
            types[name] = q
            return q
        }

        //Reference this seems to be the wrong place
        //if (name.length > 7 && name.substring(0, 7) == "REF_TO ")
        //    return ReferenceType(resolveDataType(name.substring(7)))

        // Void
        if (name == "VOID")
            return DataTypes.VOID

        // Enum
        val enumerateType = resolveEnum(name)
        if (enumerateType != null)
            return enumerateType

        if (this.parent != null)
            return this.parent!!.resolveDataType(name)

        throw DataTypeNotDefinedException("Could not find: $name")
        //return null;
    }

    fun resolveFunction(invocation: Invocation): FunctionDeclaration? {
        for (fr in functionResolvers) {
            val decl = fr.resolve(invocation, this)
            if (decl != null)
                return decl
        }
        return if (this.parent != null) this.parent!!.resolveFunction(invocation) else null
    }

    fun registerClass(clazz: ClassDeclaration) =
            classes.register(clazz.name, clazz)

    fun resolveClass(key: String) = classes.lookup(key)
    fun registerInterface(interfaceDeclaration: InterfaceDeclaration) =
            interfaces.register(interfaceDeclaration.name, interfaceDeclaration)

    fun registerMethod(md: MethodDeclaration) = methods.register(md.name, md)
    fun resolveInterface(key: String) = interfaces.lookup(key)
    fun resolveEnum(value: String) = if (allowedEnumValues.containsKey(value)) allowedEnumValues[value] else null
    fun resolveAction(name: String) = actions.lookup(name)
    fun registerAction(a: ActionDeclaration) = actions.register(a.name, a)

    fun resolveVariable(variable: SymbolicReference): VariableDeclaration? {
        if (variable.identifier in variables) {
            return variables[variable.identifier]
        } else {
            return parent?.resolveVariable(variable)
        }
    }


    fun isGlobalVariable(variable: SymbolicReference): Boolean {
        return topLevel?.resolveVariable(variable) != null
    }

    override fun clone(): Scope {
        val gs = Scope(parent)
        gs.classes = Namespace(classes)
        gs.interfaces = Namespace(interfaces)
        gs.dataTypes = Namespace<TypeDeclaration>(dataTypes)
        gs.functionBlocks = Namespace(functionBlocks)
        gs.functionResolvers = ArrayList(functionResolvers)
        gs.functions = Namespace(functions)
        gs.programs = Namespace(programs)
        gs.types = types.clone()
        for (vd in variables)
            gs.add(vd.clone())
        return gs
    }

    /**
     * @return a shallow clone of the scope (all elements are the same)
     */
    fun shallowCopy(): Scope {
        val gs = Scope(parent)
        gs.classes = Namespace(classes)
        gs.interfaces = Namespace(interfaces)
        gs.dataTypes = Namespace<TypeDeclaration>(dataTypes)
        gs.functionBlocks = Namespace(functionBlocks)
        gs.functionResolvers = ArrayList(functionResolvers)
        gs.functions = Namespace(functions)
        gs.programs = Namespace(programs)
        gs.types = types.clone()
        gs.variables.addAll(variables)
        return gs
    }

    fun addVariables(scope: Scope) {
        variables.addAll(scope.variables)
    }


    fun filterByFlags(vararg flag: Int): List<VariableDeclaration> {
        return variables.filter { it ->
            flag.find { f -> it.isType(f) } != null
        }
    }

    companion object {
        fun defaultScope(): Scope {
            val g = Scope()
            g.functionResolvers.add(DefinedFunctionResolver())
            g.functionResolvers.add(FunctionResolverMUX())
            return g
        }
    }
}

class Namespace<T : Identifiable>() {
    private val map: LookupList<T> = LookupList()
    internal var parent: Supplier<Namespace<T>>? = null

    fun streamAll(): Stream<T> =
            if (parent?.get() != null)
                Stream.concat(parent!!.get().streamAll(), map.stream())
            else map.stream()

    internal constructor(other: Namespace<T>) : this() {
        map.addAll(other.map)
        parent = other.parent
    }

    internal fun lookup(key: String): T? {
        val v = map[key]
        if (v != null) return v
        return if (parent?.get() != null) parent!!.get().lookup(key) else null
    }

    internal fun register(key: String, obj: T) {
        if (key == "")
            throw IllegalArgumentException("Registering empty string isType not allowed")
        map += obj
    }

    fun containsKey(name: String) = map[name] != null

    fun values(): Collection<T> {
        return map
    }

}
