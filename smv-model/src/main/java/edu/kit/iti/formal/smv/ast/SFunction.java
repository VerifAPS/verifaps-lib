package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
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

import edu.kit.iti.formal.smv.FunctionTypeSolver;
import edu.kit.iti.formal.smv.SMVAstVisitor;

import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class SFunction extends SMVExpr {
    private final List<SMVExpr> arguments;
    private final String functionName;
    private FunctionTypeSolver typeSolver;

    public SFunction(String funcName, SMVExpr... expr) {
        this.functionName = funcName;
        this.arguments = Arrays.asList(expr);
    }

    public SFunction(String text, List<SMVExpr> exprs) {
        this.functionName = text;
        this.arguments = exprs;
    }

    public List<SMVExpr> getArguments() {
        return arguments;
    }

    public String getFunctionName() {
        return functionName;
    }

    public FunctionTypeSolver getTypeSolver() {
        return typeSolver;
    }

    public void setTypeSolver(FunctionTypeSolver typeSolver) {
        this.typeSolver = typeSolver;
    }

    @Override
    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public SMVType getSMVType() {
        return typeSolver.getDataType(this);
    }

    @Override
    public String toString() {
        return functionName + "(" + arguments + ")";
    }
}
