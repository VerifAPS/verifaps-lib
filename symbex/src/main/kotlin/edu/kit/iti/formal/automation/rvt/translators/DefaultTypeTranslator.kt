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
package edu.kit.iti.formal.automation.rvt.translators

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.exceptions.IllegalTypeException
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.SMVWordType

/**
 * Created by weigl on 11.12.16.
 */
class DefaultTypeTranslator : TypeTranslator {

    override fun translate(datatype: AnyDt): SMVType {
        val dtv = DefaultTranslatorVisitor()
        return datatype.accept(dtv)
    }

    internal inner class DefaultTranslatorVisitor : DataTypeVisitorNN<SMVType> {
        override fun defaultVisit(obj: Any) = throw IllegalStateException("Not implemented for $obj")

        override fun visit(real: AnyReal) = SMVTypes.FLOAT
        override fun visit(real: AnyReal.REAL) = SMVTypes.FLOAT
        override fun visit(real: AnyReal.LREAL) = SMVTypes.FLOAT

        override fun visit(anyBit: AnyBit): SMVType = if (anyBit === AnyBit.BOOL) {
            SMVTypes.BOOLEAN
        } else {
            SMVWordType(false, anyBit.bitLength)
        }

        override fun visit(dateAndTime: AnyDate.DATE_AND_TIME): SMVType = throw IllegalTypeException("Could not match")

        override fun visit(timeOfDay: AnyDate.TIME_OF_DAY): SMVType {
            return SMVWordType(true, WORD_LENGTH)
            // throw new IllegalTypeException("Could not match");
        }

        override fun visit(date: AnyDate.DATE): SMVType = throw IllegalTypeException("Could not match")

        override fun visit(anyInt: AnyInt): SMVType {
            /*TODO: Make this configurable
            return new SMVType.SMVTypeWithWidth(
                inttype.isSigned() ?
                        GroundDataType.SIGNED_WORD :
                        GroundDataType.UNSIGNED_WORD, inttype.getBitLength());
             */
            return SMVWordType(anyInt.isSigned, anyInt.bitLength)
        }

        override fun visit(enumerateType: EnumerateType): SMVType =
            EnumType(enumerateType.allowedValues.keys.toMutableList())

        override fun visit(timeType: TimeType): SMVType = SMVWordType(true, WORD_LENGTH)

        override fun visit(rangeType: RangeType): SMVType {
            // TODO base types other than SINT
            // TODO variable width (needs to match with values everywhere)
            return SMVWordType(true, WORD_LENGTH)
        }

        override fun visit(recordType: RecordType): SMVType = throw IllegalTypeException("Could not match $recordType")

        override fun visit(pointerType: PointerType): SMVType =
            throw IllegalTypeException("Could not match$pointerType")

        override fun visit(string: IECString.STRING): SMVType = throw IllegalTypeException("Could not match$string")

        override fun visit(wString: IECString.WSTRING): SMVType = throw IllegalTypeException("Could not match")

        override fun visit(arrayType: ArrayType): SMVType = throw IllegalTypeException("Could not match")

        override fun visit(anyNum: AnyNum): SMVType = throw IllegalTypeException("Could not match: $anyNum")

        override fun visit(classDataType: ClassDataType): SMVType {
            TODO()
        }
    }

    companion object {
        val INSTANCE = DefaultTypeTranslator()
        private val WORD_LENGTH = 16
    }
}