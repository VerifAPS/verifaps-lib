package edu.kit.iti.formal.automation.smt

/*-
 * #%L
 * cexplorer
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SSymbol
import edu.kit.iti.formal.smv.SMVAstVisitor
import edu.kit.iti.formal.smv.ast.*

/**
 * @author Alexander Weigl
 * @version 1 (27.01.17), 2 (15.10.17)
 */
class SSA2SMT(val input: SMVModule) : Runnable {
    val product = SMTProgram()
    var dtTranslator: S2SDataTypeTranslator = DefaultS2STranslator()
    var fnTranslator: S2SFunctionTranslator = DefaultS2SFunctionTranslator()

    override fun run() {
        val v = Smv2SmtVisitor(fnTranslator, dtTranslator)

        //rewrite initial assignments
        input.initAssignments.forEach { (target, expr) ->
            product.initPredicates[target.name] = expr.accept(v)
        }

        //rewrite next assignments
        input.nextAssignments.forEach { (target, expr) ->
            product.nextPredicates[target.name] = expr.accept(v)
        }

        //define state values
        input.stateVars.forEach {
            product.stateDataTypes[it.name] = this.dtTranslator.translate(it.dataType!!)
        }

        //define input values
        input.moduleParameters.forEach {
            product.inputDataTypes[it.name] = this.dtTranslator.translate(it.dataType!!)
        }
    }
}

class Smv2SmtVisitor(val fnTranslator: S2SFunctionTranslator,
                     val dtTranslator: S2SDataTypeTranslator,
                     val statePrefix: String = SMTProgram.STATE_NAME) : SMVAstVisitor<SExpr> {
    override fun visit(top: SMVAst): SExpr {
        throw IllegalStateException("illegal AST node discovered!")
    }

    override fun visit(v: SVariable): SExpr {
        /*SExpr access = newNonAtomicSExpr();
        access.add(SSymbol(v.getName()));
        access.add(SSymbol(SMTProgram.STATE_NAME));
        */
        return SSymbol(statePrefix + v.name)
    }

    override fun visit(be: SBinaryExpression): SExpr {
        val left = be.left.accept(this)
        val right = be.right.accept(this)
        val op = fnTranslator.translateOperator(be.operator,
                be.left.dataType!!, be.right.dataType!!)

        val call = SList()
        call.add(op)
        call.add(left)
        call.add(right)
        return call
    }

    override fun visit(ue: SUnaryExpression): SExpr {
        val right = ue.expr.accept(this)
        val op = fnTranslator.translateOperator(ue.operator, ue.expr.dataType!!)
        val call = SList()
        call.add(op)
        call.add(right)
        return call
    }

    override fun visit(l: SLiteral): SExpr {
        return dtTranslator.translate(l)
    }

    override fun visit(a: SAssignment): SExpr {
        throw IllegalStateException("illegal AST node discovered!")
    }

    override fun visit(ce: SCaseExpression): SExpr {
        return ifThenElse(ce.cases, 0)
    }

    override fun visit(func: SFunction): SExpr {
        val args = func.arguments.map { arg -> arg.accept(this) }
        return fnTranslator.translateOperator(func, args)
    }

    override fun visit(smvModule: SMVModule): SExpr {
        throw IllegalStateException("illegal AST node discovered!")
    }


    override fun visit(quantified: SQuantified): SExpr {
        throw IllegalStateException("illegal AST node discovered! SQuantified not allowed in assignments")
    }

    private fun ifThenElse(cases: List<SCaseExpression.Case>, n: Int): SExpr {
        if (n >= cases.size) {
            throw IllegalArgumentException()
        }

        if (n == cases.size - 1) {//last element
            // ignoring the last condition for well-definedness
            return cases[n].then.accept(this)
        }

        val ite = SList()
        ite.add(SSymbol("ite"))
        ite.add(cases[n].condition.accept(this))
        ite.add(cases[n].then.accept(this))
        ite.add(ifThenElse(cases, n + 1))
        return ite
    }
}