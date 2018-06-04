package edu.kit.iti.formal.automation.st

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.06.18)
 */

import edu.kit.iti.formal.automation.st.ast.*

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


