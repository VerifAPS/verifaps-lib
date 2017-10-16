package edu.kit.iti.formal.automation.smv.translators;

import edu.kit.iti.formal.automation.datatypes.values.Value;
import edu.kit.iti.formal.automation.st.ast.Literal;
import edu.kit.iti.formal.smv.ast.SLiteral;
import lombok.Getter;
import lombok.Setter;

import javax.annotation.Nonnull;
import java.lang.reflect.Type;

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
public class DefaultValueTranslator implements ValueTranslator {
    public static final ValueTranslator INSTANCE = new DefaultValueTranslator();
    @Getter
    @Setter
    private TypeTranslator tt = DefaultTypeTranslator.INSTANCE;

    @Override
    public SLiteral translate(Value init) {
        return SLiteral.create(init.getValue()).as(tt.translate(init.getDataType()));
    }
}
