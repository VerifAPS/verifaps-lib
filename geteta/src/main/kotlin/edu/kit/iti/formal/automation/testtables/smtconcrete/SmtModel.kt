package edu.kit.iti.formal.automation.testtables.smtconcrete

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.rvt.translators.TypeTranslator
import edu.kit.iti.formal.automation.smt.DefaultS2SFunctionTranslator
import edu.kit.iti.formal.automation.smt.DefaultS2STranslator
import edu.kit.iti.formal.automation.smt.S2SDataTypeTranslator
import edu.kit.iti.formal.automation.smt.S2SFunctionTranslator
import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SExprFacade.sexpr
import edu.kit.iti.formal.smt.SInteger
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SSymbol

class SmtModel {
    val file: MutableList<SExpr> = ArrayList()

    var fnTranslator: S2SFunctionTranslator = DefaultS2SFunctionTranslator()
    var dtTranslator: S2SDataTypeTranslator = DefaultS2STranslator()
    var typeTranslator: TypeTranslator = DefaultTypeTranslator()


    fun declare(name: String, dataType: SExpr) {
        val e = sexpr("declare-const", name, dataType)
        file.add(e)

    }

    fun declare(name: String, dataType: AnyDt) {
        declare(name, dtTranslator.translate(typeTranslator.translate(dataType)))
    }

    fun assert(constr: SExpr) {
        file.add(sexpr("assert", constr))
    }

    fun bvOf(lower: Int, bitLength: Int) =
            SList(SList(SSymbol("_"), SSymbol("int2bv"), SInteger(bitLength)), SInteger(lower))


    val sexp: MutableCollection<SmtStatement> = arrayListOf()
    val asSexp: String
        get() = sexp.joinToString("\n") { it.toString() }
}

sealed class SmtStatement {
    //abstract val asSexp: Sexp
}

data class SmtConstDeclaration(val name: String, val type: String)
    : SmtStatement() {
    override fun toString(): String =
            "(declare-const $name $type)"
}