package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
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

    override fun visit(real: AnyReal.Real): T? {
        return null
    }

    override fun visit(real: AnyReal.LReal): T? {
        return null
    }

    override fun visit(anyBit: AnyBit): T? {
        return null
    }

    override fun visit(dateAndTime: AnyDate.DateAndTime): T? {
        return null
    }

    override fun visit(timeOfDay: AnyDate.TimeOfDay): T? {
        return null
    }

    override fun visit(date: AnyDate.Date): T? {
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

    override fun visit(referenceType: ReferenceType): T? {
        return null
    }

    override fun visit(string: IECString.String): T? {
        return null
    }

    override fun visit(wString: IECString.WString): T? {
        return null
    }

    override fun visit(iecArray: IECArray): T? {
        return null
    }

    override fun visit(anyNum: AnyNum): T? {
        return null
    }

    override fun visit(classDataType: ClassDataType): T? {
        return null
    }
}
