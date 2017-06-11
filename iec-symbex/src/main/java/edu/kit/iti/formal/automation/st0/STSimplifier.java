package edu.kit.iti.formal.automation.st0;

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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st0.trans.*;

import java.util.*;
import java.util.function.Function;

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 1
 */
public class STSimplifier {
    public static final int PROGRAM_VARIABLE =
            VariableDeclaration.FIRST_FREE << 1;
    private List<TopLevelElement> inputElements;

    private ProgramDeclaration theProgram;
    private Map<String, FunctionBlockDeclaration> functionBlocks = new HashMap<>();
    private TypeDeclarations allTypeDeclaration = new TypeDeclarations();

    public STSimplifier(List<TopLevelElement> inputElements) {
        this.inputElements = inputElements;
    }


    public void transform() {
        step0();
        step1();
        //TODO unhandled cases in visitor:
        step2();
        step3();
        step4();
        step5();
    }

    private void step4() {
        ArrayEmbedder ae = new ArrayEmbedder();
        theProgram = (ProgramDeclaration) theProgram.visit(ae);
    }

    private void step5() {
        SFCResetReplacer srr = new SFCResetReplacer();
        theProgram = (ProgramDeclaration) theProgram.visit(srr);
    }

    public TopLevelElements getProcessed() {
        TopLevelElements l = new TopLevelElements();
        l.add(allTypeDeclaration);
        l.add(theProgram);
        return l;
    }

    /**
     * embedding of fb into fb and fb into theProgram
     */
    private void step1() {
        for (FunctionBlockDeclaration fbd : functionBlocks.values()) {
            StatementList newStatements = embeddFunctionBlocks(fbd.getLocalScope(), fbd.getFunctionBody());
            fbd.setFunctionBody(newStatements);
        }

        for (VariableDeclaration vd : theProgram.getLocalScope().getLocalVariables().values()) {
            vd.setType(vd.getType() | PROGRAM_VARIABLE);
        }

        theProgram.setProgramBody(embeddFunctionBlocks(theProgram.getLocalScope(), theProgram.getProgramBody()));
    }

    private void step2() {
        TimerToCounter ttc = new TimerToCounter(4);
        //TODO to be defined by console
        theProgram = (ProgramDeclaration) ttc.visit(theProgram);
    }

    /**
     * Unwinding loop
     */
    private void step3() {
        LoopUnwinding loopUnwinding = new LoopUnwinding();
        theProgram = (ProgramDeclaration) theProgram.visit(loopUnwinding);
    }

    private StatementList embeddFunctionBlocks(LocalScope declared, StatementList statements) {
        Set<VariableDeclaration> decls =
                new HashSet<>(declared.getLocalVariables().values());
        for (VariableDeclaration vd : decls) {
            String typeName = vd.getDataTypeName();
            Any type = vd.getDataType();

            if (type instanceof FunctionBlockDataType) {
                FunctionBlockDataType fbdType = (FunctionBlockDataType) type;
                FunctionBlockDeclaration fbd = fbdType.getFunctionBlock();
                statements = embeddFunctionBlocksImpl(declared, statements, vd,
                        fbd);
            }
        }
        return statements;
    }

    private LocalScope prefixNames(LocalScope scope, String s) {
        LocalScope copy = new LocalScope();
        for(VariableDeclaration vd : scope) {
        	VariableDeclaration nd = new VariableDeclaration(vd);
        	if(nd.isInput() || nd.isInOut() || nd.isOutput()) {
        		int mask =
        			VariableDeclaration.INPUT |
        			VariableDeclaration.INOUT |
        			VariableDeclaration.OUTPUT;
        		nd.setType((nd.getType() & ~mask) | VariableDeclaration.LOCAL);
        	}
        	nd.setName(s + nd.getName());
            copy.add(nd);
        }
        return copy;
    }

    
    private StatementList embeddFunctionBlocksImpl(LocalScope origin, StatementList intoStatements,
                                                   VariableDeclaration vd, FunctionBlockDeclaration fbd) {
        final String prefix = vd.getName() + "$";
        LocalScope embeddVariables = prefixNames(fbd.getLocalScope(), prefix);

        //declare new variables
        origin.getLocalVariables().putAll(embeddVariables.getLocalVariables());

        // remove FunctionBlock Instance
        origin.getLocalVariables().remove(vd.getName());

        //rename function
        Function<String, String> newName = (String s) -> {
            return prefix + s;
        };

        //Make a copy of the statements and add prefix to every variable
        VariableRenamer vr = new VariableRenamer(fbd.getFunctionBody(), newName);
        StatementList sl = vr.rename(); // <- this can be injected

        // inject into every function block call
        FunctionBlockEmbedder fbe = new FunctionBlockEmbedder(vd.getName(), sl, newName);
        return fbe.embedd(intoStatements);
    }

    /**
     * Register FUNCTION AND FUNCTIONBLOCKS
     */
    public void step0() {
        int programs = 0;
        for (TopLevelElement tle : inputElements) {
            if (tle instanceof ProgramDeclaration) {
                programs++;
                theProgram = (ProgramDeclaration) tle;
            } else if (tle instanceof FunctionBlockDeclaration) {
                FunctionBlockDeclaration declaration = (FunctionBlockDeclaration) tle;
                functionBlocks.put(declaration.getFunctionBlockName(), declaration);
            } else if (tle instanceof TypeDeclarations) {
                TypeDeclarations typeDeclarations = (TypeDeclarations) tle;
                appendTypeDeclarations(typeDeclarations);
            } else if (tle instanceof FunctionDeclaration) {
                //FunctionDeclaration functionDeclaration = (FunctionDeclaration) tle;
                //functions
            } else {
                throw new IllegalArgumentException("TLE: " + tle.getClass() + " is not handled yet.");
            }
        }

        if (programs != 1) {
            System.out.println(inputElements.size());
            throw new IllegalArgumentException("There must be exactly one program in the List of TLE. " + programs + " found. Elements: " + inputElements.size());
        }
    }

    private void appendTypeDeclarations(TypeDeclarations typeDeclarations) {
        for (TypeDeclaration td : typeDeclarations) {
            boolean allowed = true;
            switch (td.getBaseTypeName()) {
                case "SINT":
                case "INT":
                case "LINT":
                case "DINT":
                case "UINT":
                case "USINT":
                case "ULINT":
                case "UDINT":
                case "BOOL":
                case "ENUM":
                    allowed = true;
                    break;
                default:
                    allowed = false;
                    break;

            }
            if (allowed)
                allTypeDeclaration.add(td);
            else
                throw new IllegalArgumentException("There is an unsupported type declared! " + td.getTypeName() + " with baseType type " + td.getBaseTypeName());
        }
    }
}
