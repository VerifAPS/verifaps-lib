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

import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.SimplifierPipelineST0
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

/**
 * @author Alexander Weigl
 * @version 2 (12.12.16)
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

    fun getDefaultSimplifier(): SimplifierPipelineST0 =
            SimplifierPipelineST0()
                    .addGlobalVariableListEmbedding()
                    .addCallEmbedding()
                    .addLoopUnwinding()
                    .addArrayEmbedding()
                    .addStructEmbedding()
                    .addTimerToCounter()

    fun simplify(exec: PouExecutable): PouExecutable {
        val stSimplifier = getDefaultSimplifier()
        return stSimplifier.transform(exec)
    }

    fun simplify(elements: PouElements): PouElements {
        val stSimplifier = getDefaultSimplifier()
        val p = PouElements()
        elements.filter { it is PouExecutable }
                .map { it as PouExecutable }
                .map(stSimplifier::transform)
                .forEach { p.add(it) }
        return p
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


    @JvmOverloads
    fun evaluateProgram(exec: PouExecutable, skipSimplify: Boolean = false): SMVModule {
        val elements = exec.scope.getVisiblePous()
        IEC61131Facade.resolveDataTypes(PouElements(elements.toMutableList()), exec.scope.topLevel)
        val a = if (skipSimplify) exec else simplify(exec)

        val se = SymbolicExecutioner(exec.scope.topLevel)
        a.accept(se)

        val moduleBuilder = ModuleBuilder(exec, se.peek())
        moduleBuilder.run()
        return moduleBuilder.module
    }

    @JvmOverloads
    fun evaluateProgram(elements: PouElements, skipSimplify: Boolean = false): SMVModule {
        val a = if (skipSimplify) elements else simplify(elements)
        return evaluateProgram(Utils.findProgram(a)
                ?: throw IllegalStateException("Could not find any program in the given set of POUs"), skipSimplify)
    }

    fun asSVariable(vd: VariableDeclaration): SVariable {
        return DefaultTypeTranslator().translate(vd)
    }
}
