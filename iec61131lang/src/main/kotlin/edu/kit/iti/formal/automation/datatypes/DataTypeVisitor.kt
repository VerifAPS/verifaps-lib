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
 * @param <T> return type
 * @author Alexander Weigl, Augusto Modanese
</T> */

interface DataTypeVisitor<T> {
    fun defaultVisit(any: AnyDt): T? {
        return null
    }

    open fun visit(real: AnyReal): T? {
        return defaultVisit(real)
    }

    open fun visit(real: AnyReal.Real): T? {
        return defaultVisit(real)
    }

    open fun visit(real: AnyReal.LReal): T? {
        return defaultVisit(real)
    }

    open fun visit(anyBit: AnyBit): T? {
        return defaultVisit(anyBit)
    }

    open fun visit(dateAndTime: AnyDate.DateAndTime): T? {
        return defaultVisit(dateAndTime)
    }

    open fun visit(timeOfDay: AnyDate.TimeOfDay): T? {
        return defaultVisit(timeOfDay)
    }

    open fun visit(date: AnyDate.Date): T? {
        return defaultVisit(date)
    }

    fun visit(reference: AnyReference): T? {
        return defaultVisit(reference)
    }

    open fun visit(anyInt: AnyInt): T? {
        return visit(anyInt as AnyNum)
    }

    open fun visit(anyInt: AnySignedInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: AnyUnsignedInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: Int): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: SInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: DInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: LInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: UDInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: USInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: ULInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(anyInt: UInt): T? {
        return visit(anyInt as AnyInt)
    }

    open fun visit(bool: AnyBit.Bool): T? {
        return visit(bool as AnyBit)
    }

    fun visit(word: AnyBit.Byte): T? {
        return visit(word as AnyBit)
    }

    fun visit(word: AnyBit.Word): T? {
        return visit(word as AnyBit)
    }

    fun visit(word: AnyBit.DWord): T? {
        return visit(word as AnyBit)
    }

    fun visit(word: AnyBit.LWord): T? {
        return visit(word as AnyBit)
    }

    open fun visit(enumerateType: EnumerateType): T? {
        return defaultVisit(enumerateType)
    }

    open fun visit(timeType: TimeType): T? {
        return defaultVisit(timeType)
    }

    open fun visit(rangeType: RangeType): T? {
        return defaultVisit(rangeType)
    }

    open fun visit(recordType: RecordType): T? {
        return defaultVisit(recordType)
    }

    open fun visit(pointerType: PointerType): T? {
        return defaultVisit(pointerType)
    }

    open fun visit(referenceType: ReferenceType): T? {
        return defaultVisit(referenceType)
    }

    open fun visit(string: IECString.String): T? {
        return defaultVisit(string)
    }

    open fun visit(wString: IECString.WString): T? {
        return defaultVisit(wString)
    }

    open fun visit(iecArray: IECArray): T? {
        return defaultVisit(iecArray)
    }

    open fun visit(anyNum: AnyNum): T? {
        return defaultVisit(anyNum)
    }

    open fun visit(classDataType: ClassDataType): T? {
        return defaultVisit(classDataType)
    }

    fun visit(interfaceDataType: InterfaceDataType): T? {
        return defaultVisit(interfaceDataType)
    }

    fun visit(functionBlockDataType: FunctionBlockDataType): T? {
        return defaultVisit(functionBlockDataType)
    }
}
