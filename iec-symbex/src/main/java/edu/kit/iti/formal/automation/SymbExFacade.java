package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec-symbex
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.oo.OOIEC61131Facade;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.smv.ModuleBuilder;
import edu.kit.iti.formal.automation.smv.SymbolicExecutioner;
import edu.kit.iti.formal.automation.smv.SymbolicState;
import edu.kit.iti.formal.automation.smv.translators.DefaultTypeTranslator;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import edu.kit.iti.formal.automation.st0.trans.*;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public final class SymbExFacade {
    public static SMVExpr evaluateFunction(FunctionDeclaration decl, SMVExpr... args) {
        return evaluateFunction(decl, Arrays.asList(args));
    }

    public static SMVExpr evaluateFunction(FunctionDeclaration decl, List<SMVExpr> ts) {
        SymbolicExecutioner se = new SymbolicExecutioner();
        SymbolicState state = new SymbolicState();
        // <name>(i1,i2,i2,...)
        Invocation fc = new Invocation();
        fc.setCalleeName(decl.getName());
        int i = 0;
        for (VariableDeclaration vd : decl.getScope()
                .filterByFlags(VariableDeclaration.INPUT)) {
            fc.getParameters().add(new Invocation.Parameter(new SymbolicReference(vd.getName())));
            state.put(se.lift(vd), ts.get(i++));
        }
        se.push(state);
        se.getScope().getTopLevel().registerFunction(decl);
        return fc.accept(se);
    }

    /**
     * @param elements
     * @return
     */
    public static TopLevelElements simplify(TopLevelElements elements) {
        STSimplifier stSimplifier = new STSimplifier(elements);
        stSimplifier.addDefaultPipeline();
        stSimplifier.transform();
        return stSimplifier.getProcessed();
    }

    public static TopLevelElements simplifyOO(TopLevelElements elements) {
        return simplifyOO(elements, false);
    }

    /**
     * Simplify OO code.
     * @param elements the code elements
     * @param onlyOO run only OO simplifications
     * @return simplified elements
     * @see #simplify(TopLevelElements) for "classic" ST code
     */
    public static TopLevelElements simplifyOO(TopLevelElements elements, boolean onlyOO) {
        // STOO
        Scope globalScope = IEC61131Facade.resolveDataTypes(elements);
        TopLevelElement program = Utils.findProgram(elements);
        InstanceScope instanceScope = OOIEC61131Facade.findInstances(program, globalScope);
        System.out.println("Found " + instanceScope.getAllInstances().size() + " instances");
        EffectiveSubtypeScope effectiveSubtypeScope =
                OOIEC61131Facade.findEffectiveSubtypes(elements, globalScope, instanceScope);
        STOOSimplifier stooSimplifier =
                new STOOSimplifier(program, elements, globalScope, instanceScope, effectiveSubtypeScope);
        stooSimplifier.simplify();
        if (onlyOO)
            return stooSimplifier.getState().getTopLevelElements();
        // ST0
        // Pass STOO state to enable STOO-aware transformations
        STSimplifier stSimplifier = new STSimplifier(elements, stooSimplifier.getState());
        stSimplifier.addDefaultPipeline();
        stSimplifier.transform();
        return stooSimplifier.getState().getTopLevelElements();
    }

    public static void simplify(TypeDeclarations types,
                                TopLevelScopeElement tlsElement,
                                boolean unwindLoops,
                                boolean timerToCounter,
                                boolean embedArrays,
                                boolean replaceSFCReset) {

        ProgramDeclaration program = tlsElement instanceof ProgramDeclaration ?
                (ProgramDeclaration) tlsElement : null;
        FunctionBlockDeclaration fb = tlsElement instanceof FunctionBlockDeclaration ?
                (FunctionBlockDeclaration) tlsElement : null;
        FunctionDeclaration function = tlsElement instanceof FunctionDeclaration ?
                (FunctionDeclaration) tlsElement : null;

        assert program != null || fb != null || function != null;

        final ProgramDeclaration container = new ProgramDeclaration();
        container.setProgramName(tlsElement.getIdentifier());
        container.setScope(tlsElement.getScope());

        if (program != null) container.setStBody(program.getStBody());
        if (fb != null) container.setStBody(fb.getStBody());
        if (function != null) container.setStBody(function.getStBody());

        TopLevelElements elements = new TopLevelElements();
        elements.add(types);
        elements.add(container);

        final TopLevelElements simplified = simplify(
                elements, false,
                unwindLoops, timerToCounter, embedArrays, replaceSFCReset);

        ProgramDeclaration simpleProgram = null;
        for (TopLevelElement i : simplified) {
            if (i instanceof ProgramDeclaration) {
                simpleProgram = (ProgramDeclaration) i;
                break;
            }
        }
        assert simpleProgram != null;

        tlsElement.setScope(simpleProgram.getScope());
        if (program != null) program.setStBody(simpleProgram.getStBody());
        if (fb != null) fb.setStBody(simpleProgram.getStBody());
        if (function != null)
            function.setStBody(simpleProgram.getStBody());
    }

    public static TopLevelElements simplify(TopLevelElements elements,
                                            boolean embedFunctionBlocks,
                                            boolean unwindLoops,
                                            boolean timerToCounter,
                                            boolean embedArrays,
                                            boolean replaceSFCReset) {
        STSimplifier stSimplifier = new STSimplifier(elements);
        List<ST0Transformation> transformations = stSimplifier.getTransformations();

        if (embedFunctionBlocks) {
            transformations.add(new FunctionBlockEmbedding());
        }
        if (unwindLoops) {
            transformations.add(LoopUnwinding.getTransformation());
        }
        if (timerToCounter) {
            transformations.add(TimerToCounter.getTransformation());
        }
        if (embedArrays) {
            transformations.add(new ArrayEmbedder());
        }
        if (replaceSFCReset) {
            transformations.add(SFCResetReplacer.getTransformation());
        }

        stSimplifier.transform();
        return stSimplifier.getProcessed();
    }

    public static SMVModule evaluateProgram(TopLevelElements elements) {
        return evaluateProgram(elements, false);
    }

    public static SMVModule evaluateProgram(TopLevelElements elements, boolean skipSimplify) {
        TopLevelElements a = skipSimplify ? elements : simplify(elements);
        Scope globalScope = IEC61131Facade.resolveDataTypes(a);
        return evaluateProgram(Utils.findProgram(a),
                (TypeDeclarations) a.get(0), globalScope);
    }

    public static SMVModule evaluateProgram(ProgramDeclaration decl, TypeDeclarations types) {
        // If global scope is null, symbolic executioner will be instanced with the default scope
        return evaluateProgram(decl, types, null);
    }

    public static SMVModule evaluateProgram(ProgramDeclaration decl,
                                            TypeDeclarations types, Scope globalScope) {
        SymbolicExecutioner se = new SymbolicExecutioner(globalScope);
        decl.accept(se);
        ModuleBuilder moduleBuilder = new ModuleBuilder(decl, types, se.peek());
        moduleBuilder.run();
        return moduleBuilder.getModule();
    }

    public static SVariable asSVariable(VariableDeclaration vd) {
        return new DefaultTypeTranslator().translate(vd);
    }
}
