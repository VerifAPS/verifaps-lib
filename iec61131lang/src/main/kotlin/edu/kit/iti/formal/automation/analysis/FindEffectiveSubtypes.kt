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

package edu.kit.iti.formal.automation.analysis

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
            dataTypes.add((resolveReference(expression.callee).a as Invocable).returnType)
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