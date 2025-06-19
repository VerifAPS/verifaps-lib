/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation.il

import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.ANONYM
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto

/**
 *
 * @author Alexander Weigl
 * @version 1 (21.02.19)
 */
class IlPrinter(val writer: CodeWriter) : IlTraversalVisitor() {
    val stPrinter = StructuredTextPrinter(writer)

    override fun defaultVisit(top: IlAst) {
        writer.write("// Could not print out: $top")
    }

    override fun visit(variable: IlOperand.Variable) {
        variable.ref.accept(stPrinter)
    }

    override fun visit(constant: IlOperand.Constant) {
        constant.literal.accept(stPrinter)
    }

    override fun visit(jump: JumpInstr) {
        writer.write("${jump.type} ${jump.target}").nl()
    }

    override fun visit(simple: SimpleInstr) {
        writer.write("${simple.type} ")
        simple.operand?.accept(this)
        writer.nl()
    }

    override fun visit(funCall: FunctionCallInstr) {
        funCall.function.accept(stPrinter)
        writer.write(" ")
        funCall.operands.joinInto(writer, ", ") {
            it.accept(this)
        }
        writer.nl()
    }

    override fun visit(expr: ExprInstr) {
        writer.write("${expr.operand} ")
        if (expr.operandi != null && expr.instr == null) {
            expr.operandi?.also {
                it.accept(this@IlPrinter)
            }
        } else if (expr.operandi != null || expr.instr != null) {
            writer.cblock("(", ")") {
                expr.operandi?.also {
                    it.accept(this@IlPrinter)
                }
                expr.instr?.let {
                    writer.nl()
                    it.accept(this@IlPrinter)
                }
            }
        }
        writer.nl()
    }

    override fun visit(call: CallInstr) {
        if (call.type != CallOperand.IMPLICIT_CALLED) {
            writer.write("${call.type} ")
        }
        call.ref.accept(stPrinter)
        writer.cblock("(", ")") {
            call.parameters.joinInto(writer, "") {
                it.accept(this@IlPrinter)
                writer.nl()
            }
        }
        writer.nl()
    }

    override fun visit(param: IlParameter) {
        if (param.left == ANONYM) {
            param.right.accept(this)
        } else {
            if (param.negated) {
                writer.write("NOT ")
            }
            writer.write(param.left)
            writer.write(if (param.input) " := " else " => ")
            param.right.accept(this)
        }
    }
}