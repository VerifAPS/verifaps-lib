package edu.kit.iti.formal.automation.smv.dt;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;

/**
 * @author Alexander Weigl
 */
public interface TypeTranslator {
    SMVType translate(Any datatype);

    default SVariable translate(VariableDeclaration vdecl) {
        return SVariable.create(vdecl.getName()).with(translate(vdecl.getDataType()));
    }

}
