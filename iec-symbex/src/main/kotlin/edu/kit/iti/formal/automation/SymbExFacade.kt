package edu.kit.iti.formal.automation

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.STSimplifier
import edu.kit.iti.formal.automation.st0.trans.*
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
object SymbExFacade {
    fun evaluateFunction(decl: FunctionDeclaration, vararg args: SMVExpr): SMVExpr {
        return evaluateFunction(decl, Arrays.asList(*args))
    }

    fun evaluateFunction(decl: FunctionDeclaration, ts: List<SMVExpr>): SMVExpr {
        val se = SymbolicExecutioner()
        val state = SymbolicState()
        // <name>(i1,i2,i2,...)
        val fc = Invocation()
        fc.calleeName = decl.name
        var i = 0
        for (vd in decl.scope
                .filterByFlags(VariableDeclaration.INPUT)) {
            fc.parameters.add(InvocationParameter(SymbolicReference(vd.name)))
            state[se.lift(vd)] = ts[i++]
        }
        se.push(state)
        se.scope!!.topLevel.registerFunction(decl)
        return fc.accept(se) as SMVExpr
    }

    /**
     * @param elements
     * @return
     */
    fun simplify(elements: PouElements): PouElements {
        val stSimplifier = STSimplifier(elements)
        stSimplifier.addDefaultPipeline()
        stSimplifier.transform()
        return stSimplifier.processed
    }

    /*    public static PouElements simplifyOO(PouElements elements) {
        return simplifyOO(elements, false);
    }*/

    /*
     * Simplify OO code.
     *
     * @param elements the code elements
     * @param onlyOO   run only OO simplifications
     * @return simplified elements
     * @see #simplify(PouElements) for "classic" ST code
     * <p>
     * public static PouElements simplifyOO(PouElements elements, boolean onlyOO) {
     * // STOO
     * Scope globalScope = IEC61131Facade.INSTANCE.resolveDataTypes(elements);
     * PouElement program = Utils.INSTANCE.findProgram(elements);
     * InstanceScope instanceScope = OOIEC61131Facade.INSTANCE.findInstances(program, globalScope);
     * System.out.println("Found " + instanceScope.getAllInstances().size() + " instances");
     * EffectiveSubtypeScope effectiveSubtypeScope =
     * OOIEC61131Facade.INSTANCE.findEffectiveSubtypes(elements, globalScope, instanceScope);
     * STOOSimplifier stooSimplifier =
     * new STOOSimplifier(program, elements, globalScope, instanceScope, effectiveSubtypeScope);
     * stooSimplifier.simplify();
     * if (onlyOO)
     * return stooSimplifier.getState().getTopLevelElements();
     * // ST0
     * // Pass STOO state to enable STOO-aware transformations
     * STSimplifier stSimplifier = new STSimplifier(elements, stooSimplifier.getState());
     * stSimplifier.addDefaultPipeline();
     * stSimplifier.transform();
     * return stooSimplifier.getState().getTopLevelElements();
     * }
     */

    fun simplify(types: TypeDeclarations,
                 pou: PouExecutable,
                 unwindLoops: Boolean,
                 timerToCounter: Boolean,
                 embedArrays: Boolean,
                 replaceSFCReset: Boolean) {

        val elements = PouElements()
        elements.add(types)
        elements.add(pou)

        val simplified = simplify(
                elements, false,
                unwindLoops, timerToCounter, embedArrays, replaceSFCReset)

        var simpleProgram: ProgramDeclaration? = null
        for (i in simplified) {
            if (i is ProgramDeclaration) {
                simpleProgram = i
                break
            }
        }
    }

    fun simplify(elements: PouElements,
                 embedFunctionBlocks: Boolean,
                 unwindLoops: Boolean,
                 timerToCounter: Boolean,
                 embedArrays: Boolean,
                 replaceSFCReset: Boolean): PouElements {
        val stSimplifier = STSimplifier(elements)
        val transformations = stSimplifier.transformations

        if (embedFunctionBlocks) {
            transformations.add(FunctionBlockEmbedding())
        }
        if (unwindLoops) {
            transformations.add(LoopUnwinding.transformation)
        }
        if (timerToCounter) {
            transformations.add(TimerToCounter.INSTANCE)
        }
        if (embedArrays) {
            transformations.add(ArrayEmbedder())
        }
        if (replaceSFCReset) {
            transformations.add(SFCResetReplacer.transformation)
        }

        stSimplifier.transform()
        return stSimplifier.processed
    }

    @JvmOverloads
    fun evaluateProgram(elements: PouElements, skipSimplify: Boolean = false): SMVModule {
        val a = if (skipSimplify) elements else simplify(elements)
        val globalScope = IEC61131Facade.resolveDataTypes(a)
        return evaluateProgram(Utils.findProgram(a)!!,
                a[0] as TypeDeclarations, globalScope)
    }

    @JvmOverloads
    fun evaluateProgram(decl: ProgramDeclaration,
                        types: TypeDeclarations, globalScope: Scope? = null): SMVModule {
        val se = SymbolicExecutioner(globalScope)
        decl.accept(se)
        val moduleBuilder = ModuleBuilder(decl, types, se.peek())
        moduleBuilder.run()
        return moduleBuilder.module
    }

    fun asSVariable(vd: VariableDeclaration): SVariable {
        return DefaultTypeTranslator().translate(vd)
    }
}// If global scope isType null, symbolic executioner will be instanced with the default scope
