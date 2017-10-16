package edu.kit.iti.formal.automation.smv.translators;

import edu.kit.iti.formal.automation.datatypes.values.Value;
import edu.kit.iti.formal.automation.st.ast.Literal;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;

import javax.annotation.Nonnull;

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
public interface ValueTranslator {
    @Nonnull
    default SLiteral translate(@Nonnull Literal literal) {
        return translate(literal.asValue());
    }

    SLiteral translate(Value init);
}
