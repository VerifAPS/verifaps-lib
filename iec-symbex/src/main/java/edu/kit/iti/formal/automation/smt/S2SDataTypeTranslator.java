package edu.kit.iti.formal.automation.smt;

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVType;

/**
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
public interface S2SDataTypeTranslator {
    Sexp translate(SMVType datatype);

    Sexp translate(SLiteral l);
}
