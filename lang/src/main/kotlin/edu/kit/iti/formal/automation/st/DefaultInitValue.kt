package edu.kit.iti.formal.automation.st

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import java.math.BigDecimal
import java.math.BigInteger

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
object DefaultInitValue : InitValueTranslator {
    override fun getInit(type: AnyDt): Value<*, *> = type.accept(InitValueVisitor)

    object InitValueVisitor : DataTypeVisitorNN<Value<*, *>> {
        override fun defaultVisit(obj: Any): Value<*, *> = throw IllegalArgumentException("unsupported data type: $obj")


        override fun visit(reference: ReferenceDt): Value<*, *> = VNULL

        override fun visit(anyInt: AnyInt): Value<*, *> {
            return VAnyInt(anyInt, BigInteger.ZERO)
        }

        override fun visit(anyInt: AnyReal): Value<*, *> {
            return VAnyReal(anyInt, BigDecimal.ZERO)
        }

        override fun visit(bool: AnyBit.BOOL): Value<*, *> {
            return VBool(bool, false)
        }

        override fun visit(word: AnyBit): Value<*, *> {
            return VAnyBit(word, Bits(word.bitLength.toLong(), 0))
        }

        override fun visit(enumerateType: EnumerateType): Value<*, *> {
            return VAnyEnum(enumerateType, enumerateType.defValue!!)
        }

        override fun visit(rangeType: RangeType): Value<*, *> {
            return VAnyInt(rangeType.base, rangeType.default)
        }

        override fun visit(timeType: TimeType): Value<*, *> {
            return VTime(TimeType.TIME_TYPE, TimeData())
        }

        override fun visit(string: IECString.STRING): Value<*, *> {
            return VIECString(string, "")
        }

        override fun visit(wString: IECString.WSTRING): Value<*, *> {
            return VIECString(wString, "")
        }

        override fun visit(arrayType: ArrayType): Value<*, *> {
            val init = arrayType.fieldType.accept(this)
            val value = MultiDimArrayValue(arrayType, init)
            return VArray(arrayType, value)
        }

        override fun visit(classDataType: ClassDataType): Value<*, *> {
            return when (classDataType) {
                is ClassDataType.ClassDt -> RecordType(classDataType.name, classDataType.clazz.scope.variables).accept(this)
                else -> VNULL
            }
        }

        /*override fun visit(interfaceDataType: InterfaceDataType): Value<*, *> {
            return VNULL
        }*/

        override fun visit(functionBlockDataType: FunctionBlockDataType): Value<*, *> {
            return functionBlockDataType.asRecord().accept(this)
        }

        override fun visit(recordType: RecordType): Value<*, *> {
            val s = VStruct(recordType, RecordValue())
            recordType.fields.forEach {
                s.value.fieldValues[it.name] =
                        when {
                            it.initValue != null -> it.initValue!!
                            it.init != null -> it.init?.getValue()!!
                            it.dataType != null -> it.dataType?.accept(this)!!
                            else -> VVOID // throw IllegalStateException("Could not determine initial value for variable: $it")
                        }
            }
            return s
        }

        override fun visit(dateAndTime: AnyDate.DATE_AND_TIME): Value<*, *> {
            return VDateAndTime(dateAndTime, DateAndTimeData())
        }

        override fun visit(timeOfDay: AnyDate.TIME_OF_DAY): Value<*, *> {
            return VTimeOfDay(timeOfDay, TimeofDayData())
        }

        override fun visit(date: AnyDate.DATE): Value<*, *> {
            return VDate(date, DateData())
        }
    }
}

object EvaluateInitialization : AstVisitor<Value<*, *>>() {
    override fun defaultVisit(obj: Any): Value<*, *> {
        throw java.lang.IllegalArgumentException("${javaClass.name} not implemented for ${obj.javaClass.name}.")
    }

    override fun visit(arrayinit: ArrayInitialization): Value<*, *> {
        val v = arrayinit.initValues.map { it.accept(this) }
        val type = ArrayType(v[0].dataType, listOf(Range(
                IntegerLit(INT, 0.toBigInteger()),
                IntegerLit(INT, v.size.toBigInteger()))))
        return VArray(type, MultiDimArrayValue(type, v.first(), v))
    }

    override fun visit(si: StructureInitialization): Value<*, *> {
        val s = VStruct(RecordType("ANONYM"), RecordValue())
        si.initValues.forEach { name, init ->
            s.value.fieldValues[name] = init.accept(this)
        }
        return s
    }

    override fun visit(init: IdentifierInitializer): Value<*, *> {
        return VAnyEnum(init.enumType!!, init.value!!)
    }

    override fun visit(literal: Literal): Value<*, *> {
        return literal.asValue()!!
    }
}
