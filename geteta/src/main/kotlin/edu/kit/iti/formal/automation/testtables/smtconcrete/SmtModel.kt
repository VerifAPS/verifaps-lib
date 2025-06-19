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
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SNumber
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
        SList(SList(SSymbol("_"), SSymbol("int2bv"), SNumber(bitLength)), SNumber(lower))

    val sexp: MutableCollection<SmtStatement> = arrayListOf()
    val asSexp: String
        get() = sexp.joinToString("\n") { it.toString() }
}

sealed class SmtStatement {
    // abstract val asSexp: Sexp
}

data class SmtConstDeclaration(val name: String, val type: String) : SmtStatement() {
    override fun toString(): String = "(declare-const $name $type)"
}