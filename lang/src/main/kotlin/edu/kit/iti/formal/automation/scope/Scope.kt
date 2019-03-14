package edu.kit.iti.formal.automation.scope

import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.st.ArrayLookupList
import edu.kit.iti.formal.automation.st.Cloneable
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.LookupList
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
data class Scope(val variables: VariableScope = VariableScope())
    : Visitable, Iterable<VariableDeclaration>, Cloneable {
    override fun iterator(): Iterator<VariableDeclaration> = variables.iterator()
    private val allowedEnumValues = HashMap<String, EnumerateType>()

    var programs: Namespace<ProgramDeclaration> = Namespace()
    var functionBlocks: Namespace<FunctionBlockDeclaration> = Namespace()
    var functions: Namespace<FunctionDeclaration> = Namespace()
    var dataTypes: Namespace<TypeDeclaration> = Namespace()
    var functionResolvers: MutableList<FunctionResolver> = LinkedList()
    var types: TypeScope = TypeScope.builtin()
    var classes: Namespace<ClassDeclaration> = Namespace()
    var interfaces: Namespace<InterfaceDeclaration> = Namespace()
    val actions: Namespace<ActionDeclaration> = Namespace()
    val methods: Namespace<MethodDeclaration> = Namespace()


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


    val topLevel: Scope
        get() {
            var s: Scope? = this
            while (s!!.parent != null) s = s.parent
            return s
        }

    val allVisibleVariables: VariableScope
        get() {
            val vars = VariableScope()
            vars.addAll(variables)
            parent?.let {
                vars.addAll(it.allVisibleVariables)
            }
            return vars
        }


    fun getDefinedPous(): List<PouElement> {
        val p = PouElements()
        p.addAll(programs.values())
        p.addAll(functionBlocks.values())
        p.addAll(functions.values())
        p.addAll(classes.values())
        p.addAll(interfaces.values())
        return p
    }


    fun getVisiblePous(): List<PouElement> {
        val top = (parent?.getVisiblePous() ?: listOf())
        return getDefinedPous() + top
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
    sb.printf(vd.name).printf(":").printf(vd.dataType)
    if (vd.init != null) sb.printf(" := ").printf(vd.init)
    sb.printf("},")
    }
    sb.delete(sb.length - 1, sb.length)
    sb.printf("}")
    return sb.toString()
    }*/

    @Throws(VariableNotDefinedException::class)
    fun getVariable(reference: SymbolicReference): VariableDeclaration {
        if (reference.identifier in variables) {
            val vd = variables[reference.identifier]!!
            if (reference.hasSub() && vd.dataType != null) {
                val dt = vd.dataType!!
                val scope = when (dt) {
                    is FunctionBlockDataType -> dt.functionBlock.scope
                    is RecordType -> Scope(dt.fields)
                    is ClassDataType.ClassDt -> dt.clazz.scope
                    else -> throw VariableNotDefinedException(this, reference)
                }
                return scope.getVariable(reference.sub!!)
            } else {
                return vd
            }
        }
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

    internal fun <T : AnyDt?> resolveDataType0(name: String) = resolveDataType(name) as? T

    fun resolveDataType(name: String): AnyDt {
        if (types.containsKey(name))
            return types[name]!!

        val a = resolveFunctionBlock(name)
        val b = dataTypes.lookup(name)
        val c = resolveClass(name)
        val d = resolveInterface(name)

        //if (a && b || a && c || b && c) {
        val ambigue = arrayListOf(a, b, c, d)
                .map { if (it != null) 1 else 0 }
                .sum() > 1

        if (ambigue) {
            System.err.println("Ambiguity in Name Resolution for: $name")
        }

        val q = when {
            a != null -> FunctionBlockDataType(a)
            b != null -> b.getDataType(this)!!
            c != null -> ClassDataType.ClassDt(c)
            d != null -> ClassDataType.InterfaceDt(d)
            else -> null
        }
        if (q != null) {
            types[name] = q; return q
        }

        //Reference this seems to be the wrong place
        //if (name.length > 7 && name.substring(0, 7) == "REF_TO ")
        //    return ReferenceType(resolveDataType(name.substring(7)))

        // Void
        if (name.equals("VOID", true))
            return VOID

        // Enum
        val enumerateType = resolveEnum(name)
        if (enumerateType != null)
            return enumerateType

        if (this.parent != null)
            return this.parent!!.resolveDataType(name)

        throw DataTypeNotDefinedException("Could not find data type for name: $name")
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

    fun resolveMethod(name: String) = methods.lookup(name)


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
        return topLevel.resolveVariable(variable) === resolveVariable(variable)
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

    fun resolveEnumByValue(value: String): EnumerateType? =
            this.allowedEnumValues[value] ?: parent?.resolveEnumByValue(value)


    //region call resolver
    fun resolveInvocation(callee: SymbolicReference): Invoked? {
        val resolvers = listOf(
                this::resolveProgramInvocation,
                this::resolveActionInvocation,
                this::resolveFunctionBlockInvocation,
                this::resolveFunctionInvocation
                //,                this::resolveMethodInvocation
        )

        val resolved = resolvers.map { it(callee) }.filter { it != null }
        if (resolved.isEmpty())
            return null

        if (resolved.size > 1) {
            Console.warn("Ambiguous call for reference in $callee")
        }

        return resolved[0]
    }

    fun resolveProgramInvocation(callee: SymbolicReference): Invoked? {
        if (!callee.hasSub()) {
            val p = programs.lookup(callee.identifier)
            if (p != null) return Invoked.Program(p)
        }
        return null
    }

    fun resolveActionInvocation(callee: SymbolicReference): Invoked.Action? {
        if (!callee.hasSub()) {
            val a = resolveAction(callee.identifier)
            return if (a != null) Invoked.Action(a, this) else null
        }

        val subScope = resolveProgram(callee.identifier)?.scope ?: resolveSubScope(callee)
        if (subScope != null) {
            return subScope.resolveActionInvocation(callee.sub!!)
        }
        return null
    }

    fun resolveFunctionBlockInvocation(callee: SymbolicReference): Invoked.FunctionBlock? {
        if (!callee.hasSub()) {
            val a = resolveVariable(callee)
            val fb = (a?.dataType as FunctionBlockDataType?)?.functionBlock
            return if (fb != null) Invoked.FunctionBlock(fb) else null
        }
        val subScope = resolveSubScope(callee)
        if (subScope != null) {
            return subScope.resolveFunctionBlockInvocation(callee.sub!!)
        }
        return null
    }

    fun resolveFunctionInvocation(callee: SymbolicReference): Invoked.Function? {
        if (!callee.hasSub()) {
            val func = resolveFunction(callee.identifier)
            if (func != null) {
                return Invoked.Function(func)
            }
        }
        return null
    }

    /*TODO tracker, this and parent pointer
    fun resolveMethodInvocation(callee: SymbolicReference, self: ClassDataType): Invoked.Method? {
        if (!callee.hasSub()) {
            val a = resolveMethod(callee.identifier)
            return if (a != null) Invoked.Method(a) else null
        }
        val subScope = resolveSubScope(callee)
        if (subScope != null) {
            return subScope.resolveMethodInvocation(callee.sub!!)
        }
        return null
    }
    */

    //endregion


    /**
     * Tries to resolve the scope behind a reference, e.g. a function block or class instance, or a program.
     */
    fun resolveSubScope(sr: SymbolicReference): Scope? {
        val vd = resolveVariable(sr)
        val dt = vd?.dataType
        if (dt != null) {
            return when (dt) {
                is FunctionBlockDataType -> dt.functionBlock.scope
                is ClassDataType.ClassDt -> dt.clazz.scope
                else -> null
            }
        }
        return resolveProgram(sr.identifier)?.scope
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

class Namespace<T>() where T : Identifiable, T : Cloneable {
    private val map: LookupList<T> = ArrayLookupList()
    internal var parent: Supplier<Namespace<T>>? = null

    fun streamAll(): Stream<T> =
            if (parent?.get() != null)
                Stream.concat(parent!!.get().streamAll(), map.stream())
            else map.stream()

    internal constructor(other: Namespace<T>) : this() {
        other.map.forEach { register(it.name, it) }
        parent = other.parent
    }

    internal fun lookup(key: String): T? {
        val v = map[key]
        return v ?: parent?.get()?.lookup(key)
    }

    internal fun register(key: String, obj: T) {
        if (key == "")
            throw IllegalArgumentException("Registering empty string isType not allowed")

        val a = map[key]
        if (a != null) {
            map.remove(a)
        }
        map += obj
    }

    fun containsKey(name: String) = map[name] != null

    fun values(): Collection<T> {
        return map
    }

}
