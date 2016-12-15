package edu.kit.iti.formal.smv.ast;

import edu.kit.iti.formal.smv.FunctionTypeSolver;
import edu.kit.iti.formal.smv.SMVAstVisitor;

import java.util.Arrays;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class SFunction extends SMVExpr {
    private final SMVExpr[] arguments;
    private final String functionName;
    private FunctionTypeSolver typeSolver;

    public SFunction(String funcName, SMVExpr... expr) {
        this.functionName = funcName;
        this.arguments = expr;
    }

    public SMVExpr[] getArguments() {
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
        return functionName + "(" + Arrays.toString(arguments) +")";
    }
}
