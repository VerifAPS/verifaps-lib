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
    public SMTVariableFactory(FormulaManager formulaManager) {

    }

    public static String getVariable(String name, DataType type) {
        return getVariable(name, type, -1);
    }

    public static String getVariable(String name, DataType type, int timeFrame) {
        SMVType smvtype = DataTypeTranslator.INSTANCE.apply(type);
        return getVariable(name, smvtype, timeFrame);
    }

    public static String getVariable(String name, SMVType type) {
        return getVariable(name, type, -1);
    }

    public static String getVariable(String name, SMVType type, int timeFrame) {
        if (timeFrame >= 0)
            name = name + "@" + timeFrame;
        return name;
    }

}
