package edu.kit.iti.formal.smt

import edu.kit.iti.formal.smt.SExprFacade.fnapply

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.12.18)
 */
sealed class SmtType {
    abstract val type: SExpr
}

class SmtEnumType(val name: String, val values: Collection<String>) : SmtType() {
    override val type: SExpr by lazy { SSymbol(name) }
    val declaration by lazy {
        val s = values.map { SSymbol(it) }
        fnapply(
            "declare-datatypes", listOf(
                SList(),
                SList.singleton(fnapply(name, s))
            )
        )
    }
}

object SmtBoolType : SmtType() {
    override val type: SExpr by lazy { SSymbol("Bool") }
}

object SmtIntType : SmtType() {
    override val type: SExpr by lazy { SSymbol("Int") }
}

object SmtRealType : SmtType() {
    override val type: SExpr by lazy { SSymbol("Real") }
}

class SmtBitvectorType(val bits: Int) : SmtType() {
    override val type: SExpr by lazy { SSymbol("Int") }
}