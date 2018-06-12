/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

package edu.kit.iti.formal.automation.analysis

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
                    if (identifiedObjectDataType is IECArray && ref.subscripts != null)
                        identifiedObjectDataType = identifiedObjectDataType.fieldType
                    if (ref.hasSub())
                        if (identifiedObjectDataType is ClassDataType) {
                            if (refVariable.dataType !is ReferenceType && refVariable.dataType !is InterfaceDataType)
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
                if (currentTopLevelScopeElement is ClassDeclaration && OOUtils.hasMethodWithInheritance(currentTopLevelScopeElement as ClassDeclaration,
                                ref.identifier)) {
                    val method = OOUtils.getMethod(currentTopLevelScopeElement as ClassDeclaration,
                            ref.identifier)
                    ref.identifiedObject = method
                    ref.dataType = method.returnType
                } else if (currentTopLevelScopeElement is InterfaceDeclaration && OOUtils.hasMethodWithInheritance(currentTopLevelScopeElement as InterfaceDeclaration,
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
                } else if (currentTopLevelScopeElement is FunctionDeclaration && ref.identifier == (currentTopLevelScopeElement as FunctionDeclaration).name) {
                    ref.identifiedObject = currentTopLevelScopeElement
                    ref.dataType = (currentTopLevelScopeElement as FunctionDeclaration).returnType
                } else if (globalScope!!.functions.containsKey(ref.identifier)) {
                    ref.identifiedObject = globalScope.resolveFunction(ref.identifier)
                    ref.dataType = (ref.identifiedObject as FunctionDeclaration).returnType
                } else if (ref.hasSub()) {
                    if (ref.identifiedObject is VariableDeclaration
                            && identifiedObjectDataType is ClassDataType
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

                // Assert identified object is set for the reference
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