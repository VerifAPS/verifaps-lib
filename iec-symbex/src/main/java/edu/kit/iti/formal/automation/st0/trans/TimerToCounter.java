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

import edu.kit.iti.formal.automation.ValueFactory;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.AnyUInt;
import edu.kit.iti.formal.automation.datatypes.TimeType;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.datatypes.values.TimeValue;
import edu.kit.iti.formal.automation.st.ast.SimpleTypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

/**
 * @author Alexander Weigl (06.07.2014)
 * @version 1
 */
public class TimerToCounter extends AstVisitor<Object> {
    public static long DEFAULT_CYCLE_TIME = 4;
    private final long cycleTime;

    public TimerToCounter(long cycleTime) {
        this.cycleTime = cycleTime;
    }

    @Override public Object defaultVisit(Visitable visitable) {
        return visitable;
    }

    @Override
    public Object visit(VariableDeclaration vd) {
        if (vd.getDataTypeName() == "TIME" || vd.getDataType() == TimeType.TIME_TYPE) {
            VariableDeclaration newVariable = new VariableDeclaration(
                    vd.getName(), vd.getType(), AnyUInt.UINT);

            ScalarValue newVal = vd.getInit() != null ?
                    (ScalarValue) vd.getInit().visit(this) :
                    ValueFactory.makeUInt(0);

            //vd.setDataType(newVal.getDataType());
            SimpleTypeDeclaration sd = new SimpleTypeDeclaration();
            sd.setInitialization(newVal);
            //setPositions(vd.getInit(), sd);
            newVariable.setTypeDeclaration(sd);
            return newVariable;
        }
        return super.visit(vd);
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
