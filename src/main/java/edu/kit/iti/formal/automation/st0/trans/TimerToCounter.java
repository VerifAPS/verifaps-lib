package edu.kit.iti.formal.automation.st0.trans;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.TimeType;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.datatypes.values.TimeValue;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

/**
 * @author Alexander Weigl (06.07.2014)
 * @version 1
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
