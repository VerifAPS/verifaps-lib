package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.TimeType;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.datatypes.values.TimeValue;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

/**
 * @author weigla
 * @date 06.07.2014
 */
public class TimerToCounter extends AstCopyVisitor {

    private long cycleTime = 4;

    public TimerToCounter(long cycleTime) {
        this.cycleTime = cycleTime;
    }

    @Override
    public Object visit(VariableDeclaration vd) {
        vd = (VariableDeclaration) super.visit(vd);
        if (vd.getDataTypeName() == "TIME" || vd.getDataType() == TimeType.TIME_TYPE) {
            if (vd.getInit() != null) {
                ScalarValue newVal = (ScalarValue) ((ScalarValue) vd.getInit()).visit(this);
                vd.setDataType(newVal.getDataType());
                //TODO: vd.setInit(newVal);
            } else {
                vd.setDataType(AnyInt.INT);
            }
        }
        return vd;
    }

    @Override
    public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        if (tsScalarValue.getDataType() == TimeType.TIME_TYPE) {
            TimeValue timeValue = (TimeValue) tsScalarValue.getValue();
            long val = timeValue.asMillieseconds() / this.cycleTime;
            return new ScalarValue<>(AnyInt.getDataTypeFor((int) val, true), val);
        }
        return super.visit(tsScalarValue);
    }
}
