package edu.kit.iti.formal.automation.scope


/*-
 * #%L
 * iec61131lang
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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.analysis.ResolveDataTypes
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.sfclang.ast.ActionDeclaration
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.Cloneable
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.automation.visitors.Visitor
import org.antlr.v4.runtime.Token
import java.util.*
import java.util.function.Consumer
import java.util.function.Supplier
import java.util.stream.Collectors
import java.util.stream.Stream

/**
 * @author Alexander Weigl
 * @version 1 (13.06.14)
 */
class Scope() : Visitable, Iterable<VariableDeclaration>, Cloneable<Scope> {
    private val allowedEnumValues = HashMap<String, EnumerateType>()

    var parent: Scope? = null
        set(parent) {
            if (parent != null) {
                programs.parent = Supplier { parent.programs) }
                functionBlocks.parent = Supplier { parent.functionBlocks }
                functions.parent = Supplier { parent.functions }
                actions.parent = Supplier { parent.actions }
                classes.parent = Supplier { parent.classes }
                dataTypes.parent = Supplier<Namespace<TypeDeclaration<Any?>>> { parent.dataTypes }
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
    var dataTypes = Namespace<TypeDeclaration<*>>()
    var functionResolvers: MutableList<FunctionResolver> = LinkedList()
    var types = TypeScope.builtin()
    var classes = Namespace<ClassDeclaration>()
    var interfaces = Namespace<InterfaceDeclaration>()
    val variables: VariableScope = VariableScope(),
    val actions: Namespace<ActionDeclaration> = Namespace<ActionDeclaration>(),

    val topLevel: Scope
        get() {
            var s: Scope? = this
            while (s!!.parent != null) s = s.parent
            return s
        }

    constructor(parent: Scope) : this() {
        parent = parent
    }

    constructor(variables: List<VariableDeclaration>) : this() {
        variables.forEach { this.add(it) }
    }

    fun asMap(): Map<String, VariableDeclaration> {
        return variables
    }

    fun add(`var`: VariableDeclaration) {
        variables[`var`.name] = `var`
    }

    /**
     * {@inheritDoc}
     */
    override fun <T> accept(visitor: Visitor<T>): T {
        return visitor.visit(this)
    }

    fun prefixNames(s: String): Scope {
        val copy = Scope()
        for ((_, value) in this.variables) {
            val nd = VariableDeclaration(value)
            nd.name = s + nd.name
            copy.add(nd)
        }
        return copy
    }

    /**
     * {@inheritDoc}
     */
    override fun iterator(): Iterator<VariableDeclaration> {
        return variables.values.iterator()
    }

    override fun forEach(action: Consumer<in VariableDeclaration>) {
        variables.values.forEach(action)
    }

    /**
     * {@inheritDoc}
     */
    override fun spliterator(): Spliterator<VariableDeclaration> {
        return variables.values.spliterator()
    }

    /**
     * {@inheritDoc}
     */
    override fun toString(): String {
        val sb = StringBuilder("Scope{")
        for (s in variables.keys) {
            val vd = variables[s]
            sb.append(s).append(":").append(vd.dataType)
            if (vd.init != null) sb.append(" := ").append(vd.init)
            sb.append("},")
        }
        sb.delete(sb.length - 1, sb.length)
        sb.append("}")
        return sb.toString()
    }

    /**
     *
     * getVariable.
     *
     * @param reference a [edu.kit.iti.formal.automation.st.ast.SymbolicReference] object.
     * @return a [edu.kit.iti.formal.automation.st.ast.VariableDeclaration] object.
     * @throws edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException if any.
     */
    @Throws(VariableNotDefinedException::class)
    fun getVariable(reference: SymbolicReference): VariableDeclaration {
        // TODO does not have the same behavior as #getVariable(String) ... is this intentional?
        if (variables.containsKey(reference.identifier))
            return variables[reference.identifier]
        throw VariableNotDefinedException(this, reference)
    }

    /**
     *
     * builder.
     *
     * @return a [edu.kit.iti.formal.automation.st.ast.VariableBuilder] object.
     */
    fun builder(): VariableBuilder {
        return VariableBuilder(variables)
    }

    fun filterByFlags(flags: Int): List<VariableDeclaration> {
        return variables.values.stream().filter { v -> v.`is`(flags) }.collect<List<VariableDeclaration>, Any>(Collectors.toList())
    }

    fun getVariable(s: String): VariableDeclaration? {
        if (variables.containsKey(s)) {
            return variables[s]
        }

        return if (this.parent != null) this.parent!!.getVariable(s) else null
    }

    fun hasVariable(variable: String): Boolean {
        return variables.containsKey(variable) || this.parent != null && this.parent!!.hasVariable(variable)
    }

    fun getProgram(key: String): ProgramDeclaration? {
        return programs.lookup(key)
    }

    fun getFunctionBlock(key: String): FunctionBlockDeclaration? {
        return functionBlocks.lookup(key)
    }


    fun getFunction(key: String): FunctionDeclaration? {
        return functions.lookup(key)
    }

    fun registerProgram(programDeclaration: ProgramDeclaration) {
        programs.register(programDeclaration.name!!, programDeclaration)
    }

    fun registerFunction(functionDeclaration: FunctionDeclaration) {
        functions.register(functionDeclaration.name, functionDeclaration)
    }

    fun registerFunctionBlock(fblock: FunctionBlockDeclaration) {
        functionBlocks.register(fblock.name, fblock)
    }

    fun registerType(dt: TypeDeclaration<*>) {
        dataTypes.register(dt.typeName!!, dt)
        if (dt is EnumerationTypeDeclaration)
            dt.allowedValues.stream()
                    .map<String>(Function<Token, String> { it.getText() })
                    .forEach { v -> allowedEnumValues[v] = dt.getDataType(this) }
    }

    /**
     *
     * resolveDataType.
     *
     * @param name a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
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
            q = FunctionBlockDataType(functionBlocks.lookup(name))
            types[name] = q
            return q
        }

        if (b) {
            q = Objects.requireNonNull<TypeDeclaration<Any?>>(dataTypes.lookup(name)).getDataType(this)
            types[name] = q
            return q
        }

        if (c) {
            q = ClassDataType(Objects.requireNonNull<ClassDeclaration>(classes.lookup(name)))
            types[name] = q
            return q
        }

        if (d) {
            q = InterfaceDataType(interfaces.lookup(name))
            types[name] = q
            return q
        }

        // Reference
        if (name.length > 7 && name.substring(0, 7) == "REF_TO ")
            return ReferenceType(resolveDataType(name.substring(7)))

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

    /**
     * Used to make a class or interface to be known.
     *
     * @param clazz
     * @see ResolveDataTypes
     */
    fun registerClass(clazz: ClassDeclaration) {
        classes.register(clazz.name, clazz)
    }

    fun resolveClass(key: String): ClassDeclaration? {
        return classes.lookup(key)
    }

    fun registerInterface(interfaceDeclaration: InterfaceDeclaration) {
        interfaces.register(interfaceDeclaration.name, interfaceDeclaration)
    }

    fun resolveInterface(key: String): InterfaceDeclaration? {
        return interfaces.lookup(key)
    }

    fun resolveEnum(value: String): EnumerateType? {
        return if (allowedEnumValues.containsKey(value)) allowedEnumValues[value] else null
    }

    override fun clone(): Scope {
        val gs = Scope(parent)
        gs.classes = Namespace(classes)
        gs.interfaces = Namespace(interfaces)
        gs.dataTypes = Namespace<TypeDeclaration<Any?>>(dataTypes)
        gs.functionBlocks = Namespace(functionBlocks)
        gs.functionResolvers = ArrayList(functionResolvers)
        gs.functions = Namespace(functions)
        gs.programs = Namespace(programs)
        gs.types = types.clone()

        for ((key, value) in variables) {
            gs.variables[key] = value.clone()
        }
        return gs
    }

    /**
     * @return a shallow clone of the scope (all elements are the same)
     */
    fun shallowCopy(): Scope {
        val gs = Scope(parent)
        gs.classes = Namespace(classes)
        gs.interfaces = Namespace(interfaces)
        gs.dataTypes = Namespace<TypeDeclaration<Any?>>(dataTypes)
        gs.functionBlocks = Namespace(functionBlocks)
        gs.functionResolvers = ArrayList(functionResolvers)
        gs.functions = Namespace(functions)
        gs.programs = Namespace(programs)
        gs.types = types.clone()
        gs.variables.putAll(variables)
        return gs
    }

    fun addVariables(scope: Scope) {
        variables.putAll(scope.variables)
    }

    fun stream(): Stream<VariableDeclaration> {
        return asMap().values.stream()
    }

    fun parallelStream(): Stream<VariableDeclaration> {
        return asMap().values.parallelStream()
    }

    fun getAction(name: String): ActionDeclaration? {
        return actions.lookup(name)
    }

    fun registerAction(a: ActionDeclaration) {
        actions.register(a.name, a)
    }

    fun filterByFlags(vararg flag: Int): List<VariableDeclaration> {
        return stream()
                .filter { it ->
                    for (f in flag)
                        if (it.`is`(f)) return@stream ()
                                .filter true
                    false
                }
                .collect<List<VariableDeclaration>, Any>(Collectors.toList())
    }

    inner class Namespace<T> {
        private val map = LinkedHashMap<String, T>()
        internal var parent: Supplier<Namespace<T>>? = null

        val all: Stream<T>
            get() = if (parent != null && parent!!.get() != null) Stream.concat(parent!!.get().all, map.values.stream()) else map.values.stream()

        internal constructor(other: Namespace<T>) {
            map.putAll(other.map)
            parent = other.parent
        }

        internal constructor() {

        }

        internal fun lookup(key: String): T? {
            if (map.containsKey(key))
                return map[key]
            return if (parent != null && parent!!.get() != null) parent!!.get().lookup(key) else null
        }

        internal fun register(key: String, obj: T) {
            if (key == "")
                throw IllegalArgumentException("Registering empty string is not allowed")
            map[key] = obj
        }

        fun containsKey(name: String): Boolean {
            return map.containsKey(name)
        }

        fun values(): Collection<T> {
            return map.values
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