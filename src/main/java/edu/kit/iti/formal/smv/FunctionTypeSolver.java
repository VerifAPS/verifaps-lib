package edu.kit.iti.formal.smv;

import edu.kit.iti.formal.smv.ast.SFunction;
import edu.kit.iti.formal.smv.ast.SMVType;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public interface FunctionTypeSolver {
    SMVType getDataType(SFunction f);
}
