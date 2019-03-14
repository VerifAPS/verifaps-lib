package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.AnyReal
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import edu.kit.iti.formal.automation.datatypes.values.VAnyReal
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import java.math.BigDecimal

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.07.18)
 */
class RealToInt(factor: Int = 1, intDataType: AnyInt = INT) : MultiCodeTransformation() {
    init {
        transformations += RewriteRealDeclaration(factor, intDataType)
        transformations += RewriteRealConversions(factor, intDataType)
        transformations += RemoveConversionCalls()
    }
}

class RemoveConversionCalls : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(RemoveConversionCallsImpl) as StatementList
        return state
    }

    object RemoveConversionCallsImpl : AstMutableVisitor() {
        val regexToInt = "l?real_to_.{0,2}int".toRegex(RegexOption.IGNORE_CASE)
        val regexToReal = ".{0,2}int_to_l?real".toRegex(RegexOption.IGNORE_CASE)
        override fun visit(invocation: Invocation): Expression {
            val name = invocation.callee.identifier
            val b = regexToInt.matchEntire(name) != null || regexToReal.matchEntire(name) != null

            if (b)
                return invocation.parameters[0].expression
            else
                return invocation
        }
    }
}


class RewriteRealDeclaration(val factor: Int, val intDataType: AnyInt) : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.scope.variables.forEach {
            if (it.dataType == AnyReal.REAL)
                rewriteRealDecl(it)
            if (it.dataType == AnyReal.LREAL)
                rewriteLRealDecl(it)

        }
        return state
    }

    private fun rewriteRealDecl(it: VariableDeclaration) {
        it.dataType = intDataType
        it.typeDeclaration = SimpleTypeDeclaration(intDataType, rewriteRealLiteral(factor, intDataType, it.init as RealLit?))
        rewriteRealLiteral(factor, intDataType, it)
    }


    private fun rewriteLRealDecl(it: VariableDeclaration) {
        val dt = intDataType.next() ?: intDataType
        it.dataType = dt
        it.typeDeclaration = SimpleTypeDeclaration(dt, rewriteRealLiteral(factor, dt, it.init as RealLit?))
        rewriteRealLiteral(factor, dt, it)
    }
}


private fun rewriteRealLiteral(factor: Int, dt: AnyInt, lit: RealLit?): IntegerLit? =
        if (lit == null)
            null
        else
            IntegerLit(rewriteRealLiteral(factor, dt, lit.value))

private fun rewriteRealLiteral(factor: Int, dataType: AnyInt, value: VariableDeclaration) {
    if (value.initValue != null) {
        val (dt, v) = value.initValue as VAnyReal
        value.initValue = rewriteRealLiteral(factor, dataType, v)
    }
}

private fun rewriteRealLiteral(factor: Int, dataType: AnyInt, value: BigDecimal): VAnyInt =
        VAnyInt(dataType, value.multiply(BigDecimal(factor)).toBigInteger())


class RewriteRealConversions(val factor: Int, val intDataType: AnyInt) : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.stBody = state.stBody.accept(RealLiteralRewriter()) as StatementList
        return state
    }

    inner class RealLiteralRewriter() : AstMutableVisitor() {
        override fun visit(literal: Literal): Expression =
                when (literal) {
                    is RealLit -> {
                        rewriteRealLiteral(factor, intDataType, literal)!!
                    }
                    else -> literal
                }
    }
}
