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
interface DataTypeVisitor<out T> : DataTypeVisitorNN<T?> {
    fun defaultVisit(any: AnyDt): T? = null
}

/**
 * @param <T> return type
 * @author Alexander Weigl, Augusto Modanese
 */
interface DataTypeVisitorNN<out T> {
    fun defaultVisit(obj: Any): T
    fun visit(real: AnyReal): T = defaultVisit(real)
    fun visit(real: AnyReal.REAL): T = visit(real as AnyReal)
    fun visit(real: AnyReal.LREAL): T = visit(real as AnyReal)
    fun visit(anyBit: AnyBit): T = defaultVisit(anyBit)
    fun visit(dateAndTime: AnyDate.DATE_AND_TIME): T = defaultVisit(dateAndTime)
    fun visit(timeOfDay: AnyDate.TIME_OF_DAY): T = defaultVisit(timeOfDay)
    fun visit(date: AnyDate.DATE): T = defaultVisit(date)
    fun visit(reference: ReferenceDt): T = defaultVisit(reference)
    fun visit(anyInt: AnyInt): T = visit(anyInt as AnyNum)
    fun visit(anyInt: INT): T = visit(anyInt as AnyInt)
    fun visit(anyInt: SINT): T = visit(anyInt as AnyInt)
    fun visit(anyInt: DINT): T = visit(anyInt as AnyInt)
    fun visit(anyInt: LINT): T = visit(anyInt as AnyInt)
    fun visit(anyInt: UDINT): T = visit(anyInt as AnyInt)
    fun visit(anyInt: USINT): T = visit(anyInt as AnyInt)
    fun visit(anyInt: ULINT): T = visit(anyInt as AnyInt)
    fun visit(anyInt: UINT): T = visit(anyInt as AnyInt)
    fun visit(bool: AnyBit.BOOL): T = visit(bool as AnyBit)
    fun visit(word: AnyBit.BYTE): T = visit(word as AnyBit)
    fun visit(word: AnyBit.WORD): T = visit(word as AnyBit)
    fun visit(word: AnyBit.DWORD): T = visit(word as AnyBit)
    fun visit(word: AnyBit.LWORD): T = visit(word as AnyBit)
    fun visit(enumerateType: EnumerateType): T = defaultVisit(enumerateType)
    fun visit(timeType: TimeType): T = defaultVisit(timeType)
    fun visit(rangeType: RangeType): T = defaultVisit(rangeType)
    fun visit(recordType: RecordType): T = defaultVisit(recordType)
    fun visit(pointerType: PointerType): T = defaultVisit(pointerType)
    fun visit(string: IECString.STRING): T = defaultVisit(string)
    fun visit(wString: IECString.WSTRING): T = defaultVisit(wString)
    fun visit(arrayType: ArrayType): T = defaultVisit(arrayType)
    fun visit(anyNum: AnyNum): T = defaultVisit(anyNum)
    fun visit(classDataType: ClassDataType): T = defaultVisit(classDataType)
    fun visit(interfaceDataType: InterfaceDataType): T = defaultVisit(interfaceDataType)
    fun visit(functionBlockDataType: FunctionBlockDataType): T = defaultVisit(functionBlockDataType)
    fun visit(void: AnyDt.VOID) : T = defaultVisit(void)
}
