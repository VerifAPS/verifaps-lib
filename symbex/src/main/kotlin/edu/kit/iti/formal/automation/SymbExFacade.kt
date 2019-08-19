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

import edu.kit.iti.formal.automation.cpp.TranslateToCpp
import edu.kit.iti.formal.automation.cpp.generateHeader
import edu.kit.iti.formal.automation.cpp.generateRunnableStub
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.SimplifierPipelineST0
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.smv.VariableReplacer
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.CodeWriter
import java.io.StringWriter
import java.util.*

/**
 * @author Alexander Weigl
 * @version 2 (12.12.16)
 */
object SymbExFacade {
    fun evaluateFunction(decl: FunctionDeclaration, vararg args: SMVExpr): SMVExpr {
        return evaluateFunction(decl, listOf(*args))
    }

    fun evaluateFunction(decl: FunctionDeclaration, ts: List<SMVExpr>): SMVExpr {
        val se = SymbolicExecutioner()
        //<name>(i1,i2,i2,...)
        for ((i, vd) in decl.scope
                .filterByFlags(VariableDeclaration.INPUT).withIndex()) {
            se.assign(vd, ts[i])
        }
        se.visit(decl as PouExecutable)
        val uf =  se.peek().unfolded()
        val v = uf.entries.find { (k,v)-> k.name == decl.name }!!.value
        return v
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
        elements.filterIsInstance<PouExecutable>()
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

    fun evaluateStatements(seq: StatementList, scope: Scope): SymbolicState {
        val program = ProgramDeclaration(scope = scope, stBody = seq)
        IEC61131Facade.resolveDataTypes(PouElements(arrayListOf(program)))
        val symbex = SymbolicExecutioner(scope)
        symbex.scope = scope
        program.accept(symbex)
        return symbex.peek()
    }

    fun evaluateExpression(sstate: SymbolicState, exc: Expression, scope: Scope): SMVExpr {
        val symbex = SymbolicExecutioner(scope)
        symbex.push(sstate)
        return exc.accept(symbex) as SMVExpr
    }

    fun evaluateExpression(ssa: Map<SVariable, SMVExpr>, exc: Expression, scope: Scope): SMVExpr {
        val ss = SymbolicState()
        ssa.forEach { (t, u) -> ss[t] = u }
        return evaluateExpression(ss, exc, scope)
    }


    fun evaluateExpression(expr: Expression, scope: Scope): SMVExpr {
        val symbex = SymbolicExecutioner(scope)
        return expr.accept(symbex) as SMVExpr
    }

    fun evaluateExpression(ssa: Map<SVariable, SMVExpr>, expr: SMVExpr): SMVExpr {
        val vr = VariableReplacer(ssa)
        println(expr)
        return expr.clone().accept(vr) as SMVExpr
    }

    fun toCpp(pous: PouElements, complete: Boolean): String {
        val out = StringWriter()
        val cout = CodeWriter(out)
        val cppVisitor = TranslateToCpp(cout)
        if (complete) generateHeader(cout)
        pous.accept(cppVisitor)
        if (complete) {
            cout.nl().nl()
            generateRunnableStub(cout, pous)
        }
        return out.toString()
    }
}

