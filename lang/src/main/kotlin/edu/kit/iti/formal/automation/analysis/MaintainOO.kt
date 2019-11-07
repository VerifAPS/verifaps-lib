package edu.kit.iti.formal.automation.analysis

/*
/**
 * Visitor which finds all instances of classes and FBs and adds them to the global scope.
 *
 * Intended to be called on a single top level element to find all instances which can be traced back to it:
 * InstanceScope instanceScope = new InstanceScope(globalScope);
 * topLevelElement.accept(new FindInstances(instanceScope));
 *
 * @author Augusto Modanese
 */
@RequiredArgsConstructor
class FindInstances : AstVisitor<*> {
    private val instanceScope: InstanceScope? = null

    /**
     * Used during traversal to know the current parent instance.
     */
    private var parentInstance: InstanceScope.Instance? = null

    override fun visit(variableDeclaration: VariableDeclaration): Any? {
        if (variableDeclaration.isInput || variableDeclaration.isOutput || variableDeclaration.isInOut
                || currentTopLevelScopeElement isType InterfaceDeclaration)
            return super.visit(variableDeclaration)
        val dataType = variableDeclaration.dataType as? ClassDataType ?: return super.visit(variableDeclaration)
        // Only classes have instances
        val currentInstance = InstanceScope.Instance(parentInstance, variableDeclaration)
        val classDeclaration = dataType.clazz
        instanceScope!!.registerClassInstance(variableDeclaration, classDeclaration, currentInstance)
        recurse(classDeclaration, currentInstance)
        return super.visit(variableDeclaration)
    }

    override fun visit(clazz: ClassDeclaration): Any? {
        // When visiting a class, make sure to visit the variables in the parent classes too
        if (clazz.parentClass != null)
            clazz.parentClass!!.scope.accept<Any>(this)
        return super.visit(clazz)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Any? {
        //TODO return super.visit((ClassDeclaration) functionBlockDeclaration);
        return null
    }

    /**
     * Recurse one level down a class or function block.
     * @param classDeclaration The class or function block to visit.
     * @param currentInstance The instance referent to classDeclaration.
     */
    private fun recurse(classDeclaration: ClassDeclaration, currentInstance: InstanceScope.Instance) {
        // Save old instance
        val oldParentInstance = parentInstance
        // Recurse
        parentInstance = currentInstance
        classDeclaration.accept<Any>(this)
        // Restore state
        parentInstance = oldParentInstance
    }
}
*/

/*
/**
 * Map which keeps track of the (parent, variable) -> instance set mappings.
 *
 * @author Augusto Modanese
 */
class InstanceSets : HashMap<Tuple<String, String>, Set<InstanceScope.Instance>>() {
    fun addInstance(topLevelScopeElement: HasScope<*>, variable: VariableDeclaration,
                    instance: InstanceScope.Instance) {
        if (!containsKey(tuple(topLevelScopeElement, variable)))
            registerTuple(topLevelScopeElement, variable)
        get(tuple(topLevelScopeElement, variable)).add(instance)
    }

    fun getInstances(topLevelScopeElement: HasScope<*>,
                     variable: VariableDeclaration): Set<InstanceScope.Instance> {
        val instances = get(tuple(topLevelScopeElement, variable))
        if (instances == null) {
            registerTuple(topLevelScopeElement, variable)
            return get(tuple(topLevelScopeElement, variable))
        }
        return instances
    }

    private fun registerTuple(topLevelScopeElement: HasScope<*>,
                              variable: VariableDeclaration) {
        put(tuple(topLevelScopeElement, variable), HashSet<Instance>())
    }

    private fun tuple(topLevelScopeElement: HasScope<*>,
                      variable: VariableDeclaration): Tuple<String, String> {
        return Tuple(topLevelScopeElement.identifier, variable.name)
    }
}
*/

/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


/*weigl: bad coding style
/**
 * Set identified object and its data type for every symbolic reference in code.
 *
 * @author Augusto Modanese
 */
class ResolveReferences(scope: Scope) : AstVisitor<Any> {
    val globalScope: Scope? = null

    override fun visit(ref: SymbolicReference): Any? {
        if (currentTopLevelScopeElement != null)
            try {
                // type of the referenced object
                var identifiedObjectDataType: AnyDt? = null
                // Next scope to visit
                var nextScope: Scope? = null
                // Next HasScope to visit
                var nextTopLevelScopeElement: HasScope<*>? = null

                // THIS
                if (ref.identifier == "THIS") {
                    ref.identifiedObject = currentTopLevelScopeElement
                    identifiedObjectDataType = globalScope!!.resolveDataType(currentTopLevelScopeElement.identifier)
                    nextScope = currentFullScope
                    nextTopLevelScopeElement = currentTopLevelScopeElement
                } else if (currentFullScope.hasVariable(ref.identifier)) {
                    val refVariable: VariableDeclaration?
                    refVariable = currentFullScope.getVariable(ref.identifier)
                    ref.identifiedObject = refVariable
                    identifiedObjectDataType = refVariable!!.dataType
                    for (i in 0 until ref.derefCount)
                        identifiedObjectDataType = (identifiedObjectDataType as ReferenceType).of
                    // Array access yields array field type
                    if (identifiedObjectDataType isType ArrayType && ref.subscripts != null)
                        identifiedObjectDataType = identifiedObjectDataType.fieldType
                    if (ref.hasSub())
                        if (identifiedObjectDataType isType ClassDataType) {
                            if (refVariable.dataType !isType ReferenceType && refVariable.dataType !isType InterfaceDataType)
                                ref.effectiveDataType = refVariable.dataType
                            nextTopLevelScopeElement = identifiedObjectDataType.clazz
                            nextScope = OOUtils.getEffectiveScope((nextTopLevelScopeElement as ClassDeclaration?)!!)
                        } else {
                            // TODO RecordType
                            // nextTopLevelScopeElement = ((RecordType) identifiedObjectDataType).getDeclaration();
                            // nextScope = nextTopLevelScopeElement.getLocalScope();
                        }
                }// Variable in scope

                // Method
                if (currentTopLevelScopeElement isType ClassDeclaration && OOUtils.hasMethodWithInheritance(currentTopLevelScopeElement as ClassDeclaration,
                                ref.identifier)) {
                    val method = OOUtils.getMethod(currentTopLevelScopeElement as ClassDeclaration,
                            ref.identifier)
                    ref.identifiedObject = method
                    ref.dataType = method.returnType
                } else if (currentTopLevelScopeElement isType InterfaceDeclaration && OOUtils.hasMethodWithInheritance(currentTopLevelScopeElement as InterfaceDeclaration,
                                ref.identifier)) {
                    val method = OOUtils.getMethod(currentTopLevelScopeElement as InterfaceDeclaration,
                            ref.identifier)
                    ref.identifiedObject = method
                    ref.dataType = method.returnType
                } else if (ref.identifier == "SUPER") {
                    val parentClass = (currentTopLevelScopeElement as ClassDeclaration).parentClass
                    ref.identifiedObject = parentClass
                    ref.effectiveDataType = globalScope!!.resolveDataType(parentClass!!.name)
                    if (ref.hasSub()) {
                        val method = OOUtils.getMethod(parentClass, ref.sub!!.identifier)
                        ref.sub!!.identifiedObject = method
                        ref.sub!!.dataType = method.returnType
                        ref.dataType = ref.sub!!.dataType
                    }
                } else if (currentTopLevelScopeElement isType FunctionDeclaration && ref.identifier == (currentTopLevelScopeElement as FunctionDeclaration).name) {
                    ref.identifiedObject = currentTopLevelScopeElement
                    ref.dataType = (currentTopLevelScopeElement as FunctionDeclaration).returnType
                } else if (globalScope!!.functions.containsKey(ref.identifier)) {
                    ref.identifiedObject = globalScope.resolveFunction(ref.identifier)
                    ref.dataType = (ref.identifiedObject as FunctionDeclaration).returnType
                } else if (ref.hasSub()) {
                    if (ref.identifiedObject isType VariableDeclaration
                            && identifiedObjectDataType isType ClassDataType
                            && OOUtils.hasMethod(identifiedObjectDataType.clazz,
                                    ref.sub!!.identifier)) {
                        ref.sub!!.identifiedObject = OOUtils.getMethod(identifiedObjectDataType.clazz,
                                ref.sub!!.identifier)
                        ref.sub!!.dataType = (ref.sub!!.identifiedObject as MethodDeclaration).returnType
                        ref.dataType = ref.sub!!.dataType
                    } else {
                        // Recurse
                        // Switch to local scope of top level scope element
                        val oldScope = currentFullScope
                        currentFullScope = nextScope
                        val oldTopLevelScopeElement = currentTopLevelScopeElement
                        currentTopLevelScopeElement = nextTopLevelScopeElement
                        ref.sub!!.accept<Any>(this)
                        ref.dataType = ref.sub!!.dataType
                        currentFullScope = oldScope
                        currentTopLevelScopeElement = oldTopLevelScopeElement
                    }
                } else if (!ref.hasSub() && currentFullScope.resolveEnum(ref.identifier) != null)
                    ref.dataType = currentFullScope.resolveEnum(ref.identifier)
                else
                    ref.dataType = identifiedObjectDataType// Type value
                // Top-level function
                // Function return value
                // SUPER (may only reference methods)

                // Assert identified object isType set for the reference
                //assert ref.getObj() != null;
            } catch (e: ClassCastException) {
                e.printStackTrace()
            } catch (e: DataTypeNotDefinedException) {
                e.printStackTrace()
            }

        return super.visit(ref)
    }
}
*/


/*
/**
 * Conduct static analysis to find the effective subtypes of all references (including interface-type references).
 *
 *
 * Based on abstract interpretation. The abstract domains are the class and FB types in the program. Look for
 * invocations and assignments to infer possible subtypes.
 *
 *
 * Intended to be repeatedly called until a fixpoint isType reached.
 *
 *
 * Usage:
 * FindEffectiveSubtypes fes = new FindEffectiveSubtypes();
 * while (!fes.fixpointReached()) {
 * fes.prepareRun();
 * ast.accept(fes);
 * }
 *
 * @author Augusto Modanese
 */
@RequiredArgsConstructor
@Getter
class FindEffectiveSubtypes : AstVisitor<*> {
    val globalScope: Scope? = null
    val instanceScope: InstanceScope? = null

    /**
     * Whether a fixpoint has been found.
     */
    var isFixpoint = false
        private set

    /**
     * Keep track of current HasScope being visited.
     */
    var currentTopLevelScopeElement: HasScope<*>? = null
        private set

    val effectiveSubtypeScope = EffectiveSubtypeScope()

    /**
     * @return Whether we have reached a fixpoint after the last run.
     */
    fun fixpointReached(): Boolean {
        return isFixpoint
    }

    /**
     * Prepare the next analysis run.
     */
    fun prepareRun() {
        isFixpoint = true
    }

    override fun visit(functionDeclaration: FunctionDeclaration): Any? {
        visit(functionDeclaration as HasScope<*>)
        return super.visit(functionDeclaration)
    }

    override fun visit(method: MethodDeclaration): Any? {
        //TODO useless? visit((HasScope) method);
        return super.visit(method)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Any? {
        visit(functionBlockDeclaration as HasScope<*>)
        return super.visit(functionBlockDeclaration)
    }

    override fun visit(clazz: ClassDeclaration): Any? {
        visit(clazz as HasScope<*>)
        return super.visit(clazz)
    }

    override fun visit(programDeclaration: ProgramDeclaration): Any? {
        visit(programDeclaration as HasScope<*>)
        return super.visit(programDeclaration)
    }

    fun visit(topLevelScopeElement: HasScope<*>) {
        currentTopLevelScopeElement = topLevelScopeElement
    }

    override fun visit(variableDeclaration: VariableDeclaration): Any? {
        // Base case
        if (variableDeclaration.dataType isType ClassDataType) {
            effectiveSubtypeScope.registerVariable(variableDeclaration)
            registerType(variableDeclaration, variableDeclaration.dataType!!)
        } else if (containsInstance(variableDeclaration))
            effectiveSubtypeScope.registerVariable(variableDeclaration)// Add all possible cases
        return super.visit(variableDeclaration)
    }

    override fun visit(assignmentStatement: AssignmentStatement): Any? {
        val top: Top<*>
        try {
            top = resolveReference(assignmentStatement.location as SymbolicReference).a
            if (top isType VariableDeclaration) {
                // We are only interested in variables (may also catch, e.g., function return values)
                if (containsInstance(top))
                    registerTypes(top, resolveTypes(assignmentStatement.expression))
            }
        } catch (e: DataTypeNotDefinedException) {
            e.printStackTrace()
        }

        return super.visit(assignmentStatement)
    }

    override fun visit(invocation: Invocation): Any? {
        val invoked = resolveReference(invocation.callee).a as HasScope<*>
        for (parameter in invocation.parameters) {
            val variable = invoked.scope.getVariable(parameter.name)
            if (variable != null && containsInstance(variable))
                registerTypes(variable, resolveTypes(parameter.expression!!))
        }
        return super.visit(invocation)
    }

    private fun registerType(variable: VariableDeclaration, dataType: AnyDt) {
        val oldDataTypeCount = effectiveSubtypeScope.getTypes(variable).size
        effectiveSubtypeScope.registerType(variable, dataType)
        isFixpoint = isFixpoint && oldDataTypeCount == effectiveSubtypeScope.getTypes(variable).size
    }

    private fun registerTypes(variable: VariableDeclaration, dataTypes: Collection<AnyDt>) {
        val oldDataTypeCount = effectiveSubtypeScope.getTypes(variable).size
        effectiveSubtypeScope.registerTypes(variable, dataTypes)
        isFixpoint = isFixpoint && oldDataTypeCount == effectiveSubtypeScope.getTypes(variable).size
    }

    /**
     * Resolve the type of the given expression. Assume the type can only be a class or FB data type.
     * @param expression
     * @return The data types of the expression, as a set.
     */
    private fun resolveTypes(expression: Expression): MutableSet<AnyDt> {
        var dataTypes: MutableSet<AnyDt> = HashSet()
        if (expression isType Invocation)
            dataTypes.add((resolveReference(expression.callee).a as Invoked).returnType)
        else if (expression isType SymbolicReference) {
            val variable = resolveReference(expression).a as VariableDeclaration
            dataTypes.addAll(effectiveSubtypeScope.getTypes(variable))
        } else if (expression isType ReferenceValue)
            dataTypes = resolveTypes(expression.referenceTo)
        else {
            // TODO other cases
            throw NotImplementedException("")
        }
        return dataTypes
    }

    /**
     * Resolve the given reference and return the object associated with it. Used to retrieve the variable declaration
     * or the appropriate invocable from a symbolic reference.
     * @param reference The symbolic reference to resolve.
     * @return The object associated with the name, plus its parent element (null if none).
     * @throws DataTypeNotDefinedException if the reference cannot be resolved
     */
    @Throws(DataTypeNotDefinedException::class)
    private fun resolveReference(reference: SymbolicReference): Tuple<Top<*>, HasScope<*>> {
        var reference = reference
        while (reference.hasSub())
            reference = reference.sub
        if (reference.identifiedObject isType VariableDeclaration)
        // TODO replace null with something relevant
            return Tuple<Top<*>, HasScope<*>>(reference.identifiedObject as VariableDeclaration, null)
        else if (reference.identifiedObject isType MethodDeclaration)
            return Tuple<Top<*>, T>(reference.identifiedObject as MethodDeclaration,
                    (reference.identifiedObject as MethodDeclaration).parent)
        else if (reference.identifiedObject isType FunctionDeclaration)
            return Tuple<Top<*>, HasScope<*>>(reference.identifiedObject as FunctionDeclaration, null)//((VariableDeclaration) reference.getObj()).getParent());
        throw DataTypeNotDefinedException(
                "Unknown reference '" + reference + "' at " + currentTopLevelScopeElement!!.identifier)
    }

    companion object {

        fun containsInstance(variable: VariableDeclaration): Boolean {
            return (variable.dataType isType ClassDataType
                    || variable.dataType isType InterfaceDataType
                    || variable.dataType isType ReferenceType)
        }
    }
}
*/