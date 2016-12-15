package edu.kit.iti.formal.automation.smv;

import com.sun.org.apache.xml.internal.security.Init;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVType;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class InitValue {
    public static final InitValue INSTANCE = new InitValue();

    public SMVExpr getInit(SMVType type) {
        //TODO
        return new SLiteral(type, 0);
    }
}
