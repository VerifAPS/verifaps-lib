package edu.kit.iti.formal.automation.testtables.concretizer;

import edu.kit.iti.formal.automation.testtables.io.DataTypeTranslator;
import edu.kit.iti.formal.automation.testtables.schema.DataType;
import edu.kit.iti.formal.smv.ast.SMVType;
import org.sosy_lab.java_smt.api.*;

/**
 * @author Alexander Weigl
 * @version 1 (31.01.17)
 */
public class SMTVariableFactory {
    private final FormulaManager fmgr;
    private final BooleanFormulaManager boolmgr;
    private final BitvectorFormulaManager bitmgr;

    public SMTVariableFactory(FormulaManager fmgr) {
        this.fmgr = fmgr;
        boolmgr = fmgr.getBooleanFormulaManager();
        bitmgr = fmgr.getBitvectorFormulaManager();
    }

    public Formula getVariable(String name, DataType type) {
        return getVariable(name, type, -1);
    }

    public Formula getVariable(String name, DataType type, int timeFrame) {
        SMVType smvtype = DataTypeTranslator.INSTANCE.apply(type);
        return getVariable(name, smvtype, timeFrame);
    }

    public Formula getVariable(String name, SMVType type) {
        return getVariable(name, type, -1);
    }

    public Formula getVariable(String name, SMVType type, int timeFrame) {
        if (timeFrame >= 0)
            name = name + "@" + timeFrame;
        if (type == SMVType.BOOLEAN)
            return boolmgr.makeVariable(name);

        SMVType.SMVTypeWithWidth wtype = (SMVType.SMVTypeWithWidth) type;
        FormulaType.BitvectorType btype = FormulaType.BitvectorType.getBitvectorTypeWithSize(wtype.getWidth());
        return bitmgr.makeVariable(btype, name);
    }

}
