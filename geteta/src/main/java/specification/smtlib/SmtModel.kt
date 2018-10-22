package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.smt.SInteger
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SSymbol

class SmtModel {
    fun declare(name: String, dataType: AnyDt) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    fun assert(translate: Any) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
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