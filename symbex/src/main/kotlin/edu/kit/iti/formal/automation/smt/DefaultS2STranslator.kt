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
package edu.kit.iti.formal.automation.smt

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.smt.*
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.SMVWordType
import edu.kit.iti.formal.smv.ast.SLiteral
import java.math.BigInteger

/**
 * Default translator for types from smv to smt. Uses bit vectors!
 *
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
class DefaultS2STranslator : S2SDataTypeTranslator {

    override fun translate(datatype: SMVType): SExpr {
        if (SMVTypes.BOOLEAN == datatype) {
            return SSymbol(SMTProgram.SMT_BOOLEAN)
        }

        if (datatype is SMVWordType) {
            val width = datatype.width
            val bv = SList()
            bv.add(SSymbol("_"))
            bv.add(SSymbol("BitVec"))
            bv.add(SSymbol(width.toString()))
            return bv
        }

        if (datatype is EnumType) {
            return SExprFacade.parseExpr("(_ BitVec 16)")
        }

        throw IllegalArgumentException()
    }

    override fun translate(l: SLiteral): SExpr {
        val dataType = l.dataType
        when (dataType) {
            SMVTypes.BOOLEAN ->
                return SSymbol(if (l.value.toString().equals("TRUE", ignoreCase = true)) "true" else "false")
            is SMVWordType -> {
                val prefix = "#b"
                val b = l.value as BigInteger
                return SSymbol("#b" + twoComplement(b, dataType.width))
            }
            is EnumType -> {
                val et = l.dataType as EnumType?
                val value = l.value as String
                val i = et!!.values.indexOf(value)
                return SSymbol("#b" + twoComplement(BigInteger.valueOf(i.toLong()), 16))
            }
            SMVTypes.INT -> {
                return SNumber(l.value as BigInteger)
            }
            else ->
                throw IllegalArgumentException("Unsupported data type: ${l.dataType}")
        }
    }

    companion object {
        fun paddedString(length: Int, fill: Char, s: String): CharArray {
            val sb = CharArray(Math.max(length, s.length))
            var i = 0
            while (i < length - s.length) {
                sb[i] = fill
                i++
            }

            var j = 0
            while (j < s.length) {
                sb[i] = s[j]
                j++
                i++
            }
            return sb
        }

        fun twoComplement(integer: BigInteger, bitLength: Int): String {
            val pos = if (integer.signum() < 0) integer.negate() else integer
            val binary = pos.toString(2)
            val b = paddedString(bitLength, '0', binary)
            if (integer.signum() < 0) {
                // complement
                for (i in b.indices) {
                    b[i] = if (b[i] == '1') '0' else '1'
                }

                // +1
                for (i in b.indices.reversed()) {
                    b[i] = (if (b[i] == '1') '0' else '1').toChar()
                    if (b[i] == '1') {
                        break
                    }
                }
            }
            return String(b)
        }
    }
}
