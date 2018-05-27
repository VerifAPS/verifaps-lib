package edu.kit.iti.formal.automation.st.util

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.IfStatement
import edu.kit.iti.formal.automation.st.ast.Statement
import edu.kit.iti.formal.automation.st.ast.StatementList

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
object Statements {

    fun ifthen(cond: Expression, then: StatementList): IfStatement {
        val statement = IfStatement()
        statement.addGuardedCommand(cond, then)
        return statement
    }

    fun ifthen(cond: Expression, vararg then: Statement): IfStatement {
        val statement = IfStatement()
        statement.addGuardedCommand(cond, StatementList(*then))
        return statement
    }

    fun ifthenelse(cond: Expression, then: Statement, otherwise: Statement): IfStatement {
        val statement = IfStatement()
        statement.addGuardedCommand(cond, StatementList(then))
        statement.elseBranch = StatementList(otherwise)
        return statement
    }

    fun ifthenelse(cond: Expression, then: StatementList, otherwise: StatementList): IfStatement {
        val statement = IfStatement()
        statement.addGuardedCommand(cond, then)
        statement.elseBranch = otherwise
        return statement
    }

}
