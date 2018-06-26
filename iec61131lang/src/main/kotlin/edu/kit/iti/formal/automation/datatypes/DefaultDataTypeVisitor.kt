package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
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

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
abstract class DefaultDataTypeVisitor<T> : DataTypeVisitor<T> {
    override fun visit(real: AnyReal): T? {
        return null
    }

    override fun visit(real: AnyReal.REAL): T? {
        return null
    }

    override fun visit(real: AnyReal.LREAL): T? {
        return null
    }

    override fun visit(anyBit: AnyBit): T? {
        return null
    }

    override fun visit(dateAndTime: AnyDate.DATE_AND_TIME): T? {
        return null
    }

    override fun visit(timeOfDay: AnyDate.TIME_OF_DAY): T? {
        return null
    }

    override fun visit(date: AnyDate.DATE): T? {
        return null
    }

    override fun visit(anyInt: AnyInt): T? {
        return null
    }

    override fun visit(enumerateType: EnumerateType): T? {
        return null
    }

    override fun visit(timeType: TimeType): T? {
        return null
    }

    override fun visit(rangeType: RangeType): T? {
        return null
    }

    override fun visit(recordType: RecordType): T? {
        return null
    }

    override fun visit(pointerType: PointerType): T? {
        return null
    }

    override fun visit(referenceType: ReferenceDt): T? {
        return null
    }

    override fun visit(string: IECString.STRING): T? {
        return null
    }

    override fun visit(wString: IECString.WSTRING): T? {
        return null
    }

    override fun visit(arrayType: ArrayType): T? {
        return null
    }

    override fun visit(anyNum: AnyNum): T? {
        return null
    }

    override fun visit(classDataType: ClassDataType): T? {
        return null
    }
}
