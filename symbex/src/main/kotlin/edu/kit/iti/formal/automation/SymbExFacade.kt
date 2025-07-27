/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.cpp.TranslateToCpp
import edu.kit.iti.formal.automation.cpp.generateHeader
import edu.kit.iti.formal.automation.cpp.generateRunnableStub
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.SimplifierPipelineST0
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.findProgram
import java.io.File
import java.io.StringWriter
import java.math.BigInteger
import kotlin.math.ceil
import kotlin.math.log2

/**
 *
 */
const val ASSERTION_PREFIX = "__assert_"

/**
 *
 */
const val ASSUMPTION_PREFIX = "__assume_"

/**
 *
 */
const val HAVOC_PREFIX = "__havoc_"

/**
 * @author Alexander Weigl
 * @version 2 (12.12.16)
 */
object SymbExFacade {
    fun evaluateFunction(decl: FunctionDeclaration, vararg args: SMVExpr): SMVExpr =
        evaluateFunction(decl, listOf(*args))

    fun evaluateFunction(decl: FunctionDeclaration, ts: List<SMVExpr>): SMVExpr {
        val se = SymbolicExecutioner()
        // <name>(i1,i2,i2,...)
        for ((i, vd) in decl.scope
            .filterByFlags(VariableDeclaration.INPUT).withIndex()) {
            se.assign(vd, ts[i])
        }
        se.visit(decl as PouExecutable)
        val uf = se.peek().unfolded()
        val v = uf.entries.find { (k, _) -> k.name == decl.name }!!.value
        return v
    }

    fun getDefaultSimplifier(): SimplifierPipelineST0 = SimplifierPipelineST0()
        .addSFCReduction()
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

    fun evaluateProgram(exec: PouExecutable, skipSimplify: Boolean = false): SMVModule =
        evaluateProgramWithLineMap(exec, skipSimplify).second

    @JvmOverloads
    fun evaluateProgramWithLineMap(exec: PouExecutable, skipSimplify: Boolean = false): Pair<LineMap, SMVModule> {
        val elements = exec.scope.getVisiblePous()
        IEC61131Facade.resolveDataTypes(PouElements(elements.toMutableList()), exec.scope.topLevel)
        val a = if (skipSimplify) exec else simplify(exec)

        val se = SymbolicExecutioner(exec.scope.topLevel)
        a.accept(se)

        val moduleBuilder = ModuleBuilder(exec, se.peek(), supportSpecialStatements = true)
        moduleBuilder.run()
        /*//debug
        for (entry in se.lineNumberMap) {
            System.out.format("%05d: %s %s\n", entry.key, entry.value.first, entry.value.second)
        }*/
        return se.lineNumberMap to moduleBuilder.module
    }

    @JvmOverloads
    fun evaluateProgram(elements: PouElements, skipSimplify: Boolean = false): SMVModule {
        val a = if (skipSimplify) elements else simplify(elements)
        return evaluateProgram(
            a.findFirstProgram()
                ?: throw IllegalStateException("Could not find any program in the given set of POUs"),
            skipSimplify,
        )
    }

    fun asSVariable(vd: VariableDeclaration): SVariable = DefaultTypeTranslator().translate(vd)

    fun evaluateStatements(seq: StatementList, scope: Scope, useDefinitions: Boolean = true): SymbolicState {
        val program = ProgramDeclaration(scope = scope, stBody = seq)
        IEC61131Facade.resolveDataTypes(PouElements(arrayListOf(program)))
        val symbex = SymbolicExecutioner(scope, useDefinitions)
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

    @JvmStatic
    fun execute(program: PouExecutable, skipSimplify: Boolean = false, cycles: Int = 10): VisualizeTrace {
        val (lineMap, mod) = evaluateProgramWithLineMap(program, skipSimplify)

        mod.name = "main"
        mod.moduleParameters.forEach { mod.inputVars.add(it) }
        mod.moduleParameters.clear()

        val counter = createCounterModule(cycles)
        mod.stateVars.add(SVariable("__counter__", ModuleType(counter.name, listOf())))
        val tmpFile = File.createTempFile("run_", ".smv")
        tmpFile.bufferedWriter().use {
            val p = SMVPrinter(CodeWriter(it))
            mod.accept(p)
            counter.accept(p)
        }
        val commandFile = File("cmd.xmv")
        writeNuxmvCommandFile(NuXMVInvariantsCommand.BMC.commands as Array<String>, commandFile)
        val p = NuXMVProcess(tmpFile, commandFile)
        val nuXmv = findProgram("nuXmv")
        if (nuXmv != null) {
            p.executablePath = nuXmv.absolutePath
        } else {
            System.getenv("NUXMV")?.let {
                p.executablePath = System.getenv("NUXMV")
            }
        }

        // use BMC because of the complete trace
        // p.commands = NuXMVInvariantsCommand.BMC.commands as Array<String>
        val output = p.call()
        if (output is NuXMVOutput.Cex) {
            val cex = output.counterExample
            return VisualizeTrace(cex, lineMap, program, CodeWriter())
        }
        throw java.lang.IllegalStateException("no counter example!")
    }

    private fun createCounterModule(k: Int): SMVModule {
        val m = SMVModule("counter$k")
        val dt = SMVWordType(false, ceil(log2(k.toDouble())).toInt())
        val cnt = SVariable("cnt", dt)
        m.stateVars.add(cnt)
        m.initAssignments.add(SAssignment(cnt, SWordLiteral(k.toBigInteger(), dt)))
        m.nextAssignments.add(SAssignment(cnt, cnt - SWordLiteral(BigInteger.ONE, dt)))
        m.invariantSpecs.add(cnt gt SWordLiteral(BigInteger.ZERO, dt))
        return m
    }
}