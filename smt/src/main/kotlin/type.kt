package edu.kit.iti.formal.smt

import edu.kit.iti.formal.smt.SExprFacade.sexpr

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
        sexpr("declare-datatypes",
                SList(), SList.singleton(SList(name, s)))
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