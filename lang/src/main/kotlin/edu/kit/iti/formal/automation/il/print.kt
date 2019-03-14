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
            if (param.negated)
                writer.write("NOT ")
            writer.write(param.left)
            writer.write(if (param.input) " := " else " => ")
            param.right.accept(this)
        }
    }
}