package edu.kit.iti.formal.smv.ast;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class SFunctionExtend extends SFunction {
    public SFunctionExtend(String funcName, SMVExpr... expr) {
        super(funcName, expr);
    }
}
