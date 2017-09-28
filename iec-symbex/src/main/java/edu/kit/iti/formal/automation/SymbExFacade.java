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

import edu.kit.iti.formal.automation.smv.dt.DataTypeTranslator;
import edu.kit.iti.formal.automation.smv.ModuleBuilder;
import edu.kit.iti.formal.automation.smv.SymbolicExecutioner;
import edu.kit.iti.formal.automation.smv.SymbolicState;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import edu.kit.iti.formal.automation.st0.trans.*;
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
        FunctionCall fc = new FunctionCall();
        fc.setFunctionName(decl.getFunctionName());
        int i = 0;
        for (VariableDeclaration vd : decl.getLocalScope()
                .filterByFlags(VariableDeclaration.INPUT)) {
            fc.getParameters().add(new SymbolicReference(vd.getName()));
            state.put(se.lift(vd), ts.get(i++));
        }
        se.push(state);
        se.getGlobalScope().registerFunction(decl);
        return fc.accept(se);
    }

    /**
     * @param elements
     * @return
     */
    public static final TopLevelElements simplify(TopLevelElements elements) {
        STSimplifier stSimplifier = new STSimplifier(elements);
        stSimplifier.transform();
        return stSimplifier.getProcessed();
    }

    public static final void simplify(TypeDeclarations types,
                                      TopLevelScopeElement tlsElement,
                                      boolean unwindLoops,
                                      boolean timerToCounter,
                                      boolean embedArrays,
                                      boolean replaceSFCReset) {

        ProgramDeclaration program = tlsElement instanceof ProgramDeclaration ?
                (ProgramDeclaration)tlsElement : null;
        FunctionBlockDeclaration fb = tlsElement instanceof FunctionBlockDeclaration ?
                (FunctionBlockDeclaration)tlsElement : null;
        FunctionDeclaration function = tlsElement instanceof FunctionDeclaration ?
                (FunctionDeclaration)tlsElement : null;

        assert program != null || fb != null || function != null;

        final ProgramDeclaration container = new ProgramDeclaration();
        container.setProgramName(tlsElement.getIdentifier());
        container.setLocalScope (tlsElement.getLocalScope());

        if(program != null) container.setProgramBody(program.getProgramBody());
        if(fb != null) container.setProgramBody(fb.getFunctionBody());
        if(function != null) container.setProgramBody(function.getStatements());

        TopLevelElements elements = new TopLevelElements();
        elements.add(types);
        elements.add(container);

        final TopLevelElements simplified = simplify(
                elements, false,
                unwindLoops, timerToCounter, embedArrays, replaceSFCReset);

        ProgramDeclaration simpleProgram = null;
        for(TopLevelElement i : simplified) {
            if(i instanceof ProgramDeclaration) {
                simpleProgram = (ProgramDeclaration)i;
                break;
            }
        }
        assert simpleProgram != null;

        tlsElement.setLocalScope(simpleProgram.getLocalScope());
        if(program != null) program.setProgramBody(simpleProgram.getProgramBody());
        if(fb != null) fb.setFunctionBody(simpleProgram.getProgramBody());
        if(function != null) function.setStatements(simpleProgram.getProgramBody());
    }

    public static final TopLevelElements simplify(TopLevelElements elements,
                                                  boolean embedFunctionBlocks,
                                                  boolean unwindLoops,
                                                  boolean timerToCounter,
                                                  boolean embedArrays,
                                                  boolean replaceSFCReset) {
        STSimplifier stSimplifier = new STSimplifier(elements);
        List<ST0Transformation> transformations = stSimplifier.getTransformations();

        if(embedFunctionBlocks) {
            transformations.add(new FunctionBlockEmbedding());
        }
        if(unwindLoops) {
            transformations.add(LoopUnwinding.getTransformation());
        }
        if(timerToCounter) {
            transformations.add(TimerToCounter.getTransformation());
        }
        if(embedArrays) {
            transformations.add(ArrayEmbedder.getTransformation());
        }
        if(replaceSFCReset) {
            transformations.add(SFCResetReplacer.getTransformation());
        }

        stSimplifier.transform();
        return stSimplifier.getProcessed();
    }

    public static final SMVModule evaluateProgram(TopLevelElements elements) {
        TopLevelElements a = simplify(elements);
        return evaluateProgram((ProgramDeclaration) a.get(1),
                (TypeDeclarations) a.get(0));
    }

    public static final SMVModule evaluateProgram(ProgramDeclaration decl,
                                                  TypeDeclarations types) {
        SymbolicExecutioner se = new SymbolicExecutioner();
        decl.accept(se);
        ModuleBuilder moduleBuilder = new ModuleBuilder(decl, types, se.peek());
        moduleBuilder.run();
        return moduleBuilder.getModule();
    }

    public static final SVariable asSVariable(VariableDeclaration vd) {
        return new DataTypeTranslator().translate(vd);
    }
}
