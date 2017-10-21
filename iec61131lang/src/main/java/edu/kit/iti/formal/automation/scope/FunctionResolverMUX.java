package edu.kit.iti.formal.automation.scope;

/*-
 * #%L
 * iec61131lang
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
import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.datatypes.promotion.DefaultTypePromoter;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 26.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class FunctionResolverMUX implements FunctionResolver {
    /**
     * {@inheritDoc}
     */
    @Override
    public FunctionDeclaration resolve(Invocation call, LocalScope scope) {
        if ("MUX".equals(call.getCalleeName())) {

            List<Any> datatypes = call.getParameters().stream().map((parameter) -> {
                try {
                    return parameter.getExpression().dataType(scope);
                } catch (VariableNotDefinedException variableNotDefinedinScope) {
                    variableNotDefinedinScope.printStackTrace();
                } catch (TypeConformityException e) {
                    e.printStackTrace();
                }
                return null;
            }).collect(Collectors.toList());
            MUXFunctionDeclaration d = new MUXFunctionDeclaration(datatypes);

            return d;


        }
        return null;
    }

    public static class MUXFunctionDeclaration extends FunctionDeclaration {

        public MUXFunctionDeclaration(List<Any> call) {
            super();
            CaseStatement stmt = new CaseStatement();
            returnType.setIdentifiedObject(call.get(1));
            DefaultTypePromoter dtp = new DefaultTypePromoter();
            for (int i = 0; i < call.size(); i++) {
                localScope.add(new VariableDeclaration("a" + i,
                        VariableDeclaration.INPUT, call.get(i)));

                if (i > 0) {
                    stmt.addCase(createCase(i));
                    returnType.setIdentifiedObject(dtp.getPromotion(
                            returnType.getIdentifiedObject(),
                            call.get(i)));
                }
            }
            statements.add(stmt);
        }

        private static CaseStatement.Case createCase(int i) {
            CaseStatement.Case c = new CaseStatement.Case();
            c.addCondition(new CaseCondition.IntegerCondition(
                    new Literal(DataTypes.INT, "" + i)));
            c.getStatements().add(new AssignmentStatement(new SymbolicReference("MUX"),
                    new SymbolicReference("a" + i)));
            return c;
        }
    }
}
