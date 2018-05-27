package edu.kit.iti.formal.automation.scope

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.DataTypes
import edu.kit.iti.formal.automation.datatypes.promotion.DefaultTypePromoter
import edu.kit.iti.formal.automation.exceptions.TypeConformityException
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException
import edu.kit.iti.formal.automation.scope.FunctionResolverMUX.MUXFunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.*
import java.util.stream.Collectors

/**
 * Created by weigl on 26.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class FunctionResolverMUX : FunctionResolver {
    /**
     * {@inheritDoc}
     */
    override fun resolve(call: Invocation, scope: Scope): FunctionDeclaration? {
        if ("MUX" == call.calleeName) {

            val datatypes = call.parameters.stream().map<AnyDt> { parameter ->
                try {
                    return@call.getParameters().stream().map parameter . expression !!. dataType scope
                } catch (variableNotDefinedinScope: VariableNotDefinedException) {
                    variableNotDefinedinScope.printStackTrace()
                } catch (e: TypeConformityException) {
                    e.printStackTrace()
                }

                null
            }.collect<List<AnyDt>, Any>(Collectors.toList())

            return MUXFunctionDeclaration(datatypes)


        }
        return null
    }

    class MUXFunctionDeclaration(call: List<AnyDt>) : FunctionDeclaration() {

        init {
            val stmt = CaseStatement()
            returnType.setIdentifiedObject(call[1])
            val dtp = DefaultTypePromoter()
            for (i in call.indices) {
                scope.add(VariableDeclaration("a$i",
                        VariableDeclaration.INPUT, call[i]))

                if (i > 0) {
                    stmt.addCase(createCase(i))
                    returnType.setIdentifiedObject(dtp.getPromotion(
                            returnType.identifiedObject,
                            call[i]))
                }
            }
            stBody.add(stmt)
        }

        private fun createCase(i: Int): CaseStatement.Case {
            val c = CaseStatement.Case()
            c.addCondition(CaseCondition.IntegerCondition(
                    Literal(DataTypes.INT, "" + i)))
            c.statements.add(AssignmentStatement(SymbolicReference("MUX"),
                    SymbolicReference("a$i")))
            return c
        }
    }
}
