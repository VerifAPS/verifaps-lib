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

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.values.Bits;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

/**
 * Created by weigl on 28/10/14.
 */
public class SFCResetReplacer extends AstCopyVisitor {

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        try {
            SymbolicReference sr = (SymbolicReference) assignmentStatement.getLocation();
            ScalarValue<AnyBit.Bool, Bits> value = (ScalarValue<AnyBit.Bool, Bits>) assignmentStatement.getExpression();

            if (sr.getIdentifier().endsWith("$SFCReset") &&
                    value.getValue().getRegister() > 0) {
                System.out.println(sr.getIdentifier());
                return new AssignmentStatement(
                        new SymbolicReference(sr.getIdentifier().replace("SFCReset", "_state")),
                        new ScalarValue<EnumerateType, String>(new EnumerateType(), "Init")
                );
            }

        } catch (ClassCastException e) {

        }
        return super.visit(assignmentStatement);
    }
}
