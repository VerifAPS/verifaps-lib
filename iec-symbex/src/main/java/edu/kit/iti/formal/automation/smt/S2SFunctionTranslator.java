package edu.kit.iti.formal.automation.smt;

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.smv.ast.SBinaryOperator;
import edu.kit.iti.formal.smv.ast.SFunction;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SUnaryOperator;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
public interface S2SFunctionTranslator {
    Sexp translateOperator(SBinaryOperator operator, SMVType typeLeft, SMVType rightType);

    Sexp translateOperator(SUnaryOperator operator, SMVType type);

    Sexp translateOperator(SFunction func, List<Sexp> args);
}
