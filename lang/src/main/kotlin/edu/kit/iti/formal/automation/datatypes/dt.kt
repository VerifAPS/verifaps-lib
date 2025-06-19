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
package edu.kit.iti.formal.automation.datatypes

import edu.kit.iti.formal.automation.*
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.st.*
import edu.kit.iti.formal.automation.st.ast.*
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*
import java.util.regex.Pattern
import kotlin.math.ceil
import kotlin.math.ln

sealed class AnyDt(override var name: String = "ANY") : Identifiable {

    constructor() : this("") {
        name = javaClass.getSimpleName().uppercase(Locale.getDefault())
    }

    abstract fun repr(obj: Any): String

    abstract fun <T> accept(visitor: DataTypeVisitorNN<T>): T

    override fun toString() = name
    open fun reprDecl(): String = "n/a"

    fun isAnonym(): Boolean = name.equals(ANONYM_DATATYPE)

    fun isAssignableTo(expected: AnyDt): Boolean = accept(DataTypeAssignability(expected))

    companion object {
        val ANONYM_DATATYPE = "ANONYM"
    }
}

object VOID : AnyDt("VOID") {
    override fun repr(obj: Any): String = TODO("not implemented")
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
open class AnyNum : AnyDt("ANY_NUM") {

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String = throw IllegalStateException("No repr for AnyNum")

    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)

    companion object {
        val ANY_NUM: AnyDt = AnyNum()
    }
}

abstract class AnyReal : AnyNum() {
    override fun repr(obj: Any): String {
        val d = obj as BigDecimal
        return name.uppercase(Locale.getDefault()) + "#" + d
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)

    object REAL : AnyReal() {
        init {
            name = "REAL"
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    object LREAL : AnyReal() {
        init {
            name = "LREAL"
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }
}

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnyBit(var bitLength: Int = 0) : AnyDt() {
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    override fun repr(obj: Any): String {
        if (obj is Bits) {
            if (obj.register > 0) {
                return (name.uppercase(Locale.getDefault()) + "#2#" + java.lang.Long.toBinaryString(obj.register))
            }
        }
        return ""
    }

    object BOOL : AnyBit(1) {
        override fun repr(obj: Any): String {
            if (obj is Bits) {
                if (obj.register > 0) {
                    return "TRUE"
                }
            }

            if (obj is Boolean) {
                if (obj) {
                    return "TRUE"
                }
            }
            return "FALSE"
        }

        override fun toString(): String = name
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    object BYTE : AnyBit(8) {
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    object WORD : AnyBit(16) {
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    object DWORD : AnyBit(32) {
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    object LWORD : AnyBit(64) {
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    companion object {
        val DATATYPES = Arrays.asList(
            AnyBit.BYTE,
            AnyBit.LWORD,
            AnyBit.WORD,
            AnyBit.DWORD,
            AnyBit.BOOL,
        )
    }
}

/**
 *
 * Abstract AnyDate class.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnyDate(name: String = "ANY_DATE") : AnyDt(name) {
    object DATE : AnyDate("DATE") {

        override fun repr(obj: Any): String {
            val dt = obj as DateData
            return String.format(
                "DATE#%4d-%2d-%2d",
                dt.year,
                dt.month,
                dt.day,
            )
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
    }

    object TIME_OF_DAY : AnyDate("TIME_OF_DAY") {
        override fun repr(obj: Any): String {
            val dt = obj as TimeofDayData
            return String.format(
                "TOD#%2d:%2d:%2d.%3d",
                dt.hours,
                dt.minutes,
                dt.seconds,
                dt.millieseconds,
            )
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
    }

    object DATE_AND_TIME : AnyDate("DATE_AND_TIME") {
        override fun repr(obj: Any): String {
            val dt = obj as DateAndTimeData
            return String.format(
                "DT#%4d-%2d-%2d-%2d:%2d:%2d.%3d",
                dt.year,
                dt.month,
                dt.day,
                dt.hours,
                dt.minutes,
                dt.seconds,
                dt.millieSeconds,
            )
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }
}

class ArrayType(
    name: String,
    val fieldType: AnyDt,
    var ranges: MutableList<Range> = ArrayList(),
) : AnyDt(name) {
    constructor(fieldType: AnyDt, ranges: List<Range>) :
        this(ANONYM_DATATYPE, fieldType, ranges.toMutableList())

    /*
    constructor(arrayTypeDeclaration: ArrayTypeDeclaration) {
        fieldType = arrayTypeDeclaration.baseType
        ranges = arrayTypeDeclaration.ranges
    }
     */

    override fun repr(obj: Any): String {
        val ary = obj as MultiDimArrayValue
        return ary.internalData().joinToString(",") { fieldType.repr(it) }
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    fun allIndices() = ranges.map { it.toIntRange() }.expand()

    fun dimSize(d: Int): Int = ranges[d].stopValue

    override fun reprDecl(): String = if (isAnonym()) {
        ranges.joinToString(", ", " ARRAY[", "] of ${fieldType.reprDecl()}") {
            "${it.startValue}..${it.stopValue}"
        }
    } else {
        name
    }
}

/**
 * Super highly complicated code, do not touch.
 */
fun List<IntRange>.expand(): Array<IntArray> {
    val span = this.map { it.last - it.first + 1 }
    val amount = span.reduce { a, b -> a * b }

    val factorRight = IntArray(size) { 0 }
    factorRight[size - 1] = 1
    for (i in (size - 2) downTo 0) {
        factorRight[i] = factorRight[i + 1] * span[i + 1]
    }

    val arrays = Array(amount) { IntArray(this.size) { -1 } }

    forEachIndexed { arrayPos, idxRange ->
        val factor = factorRight[arrayPos]
        val r = factor
        val outer = amount / span[arrayPos] / r
        var apos = 0
        repeat(outer) {
            idxRange.forEach { idx ->
                repeat(r) {
                    arrays[apos++][arrayPos] = idx
                }
            }
        }
    }
    return arrays
}

/**
 * This data type represents a class.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 04.03.17
 */
sealed class ClassDataType(name: String) : AnyDt(name) {
    object AnyClassDt : ClassDataType("BOTTOM CLASS")
    class ClassDt(val clazz: ClassDeclaration) : ClassDataType(clazz.name)
    class InterfaceDt(val clazz: InterfaceDeclaration) : ClassDataType(clazz.name)

    override fun repr(obj: Any) = TODO("not implemented") // To change body of created functions use File | Settings | File Templates.

    /* override var fields: Scope
         get() = Scope(OOUtils.getEffectiveScope(clazz).parallelStream()
                 .map<VariableDeclaration>(Function<VariableDeclaration, VariableDeclaration> { it.copy() })
                 .collect<List<VariableDeclaration>, Any>(Collectors.toList()))
         set(value: Scope) {
             super.fields = value
         }
     */

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

abstract class IECString : AnyDt() {
    object WSTRING : IECString() {
        override fun repr(obj: Any) = "WSTRING#\"$obj\""
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    /** Constant `STRING_16BIT`  */
    object STRING : IECString() {
        override fun repr(obj: Any) = "WSTRING#'$obj'"
        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }

    companion object {
        /**
         * Interprets escape chars in IEC strings.
         Escape Sequences
         The dollar sign ($) is used as an escape character to insert any character code into a string.

         Sequence	Usage	Description
         $$	Both	Dollar sign ($) character
         $'	Single	Apostrophe (') character
         $"	Double	Double quotation mark (") character
         $L	Both	Line feed (U+000A) character
         $N	Both	Line feed (U+000A) character
         $R	Both	Carriage return (U+000D) character
         $T	Both	Horizontal tab (U+0009) character
         $nn	Single	Single byte character, where nn is the two digit hexadecimal value of the character
         $nnnn	Double	Double byte character, where nnnn is the four digit hexadecimal value of the character
         */
        fun interpret(str: String): String = when {
            str.startsWith("'") -> interpret(str.trim('\''), false)
            str.startsWith("\"") -> interpret(str.trim('"'), true)
            else -> interpret(str, true)
        }

        @JvmStatic
        fun interpret(str: String, wide: Boolean): String {
            val sb = StringBuffer()
            val bytes = if (wide) 4 else 2
            val pattern = Pattern.compile("[\$]([\"'NLRTnlrt]|[0-9]{$bytes})")
            val m = pattern.matcher(str)
            while (m.find()) {
                val replacement = when (m.group(1).uppercase(Locale.getDefault())) {
                    "$" -> "$"
                    "'" -> "'"
                    "\"" -> "\""
                    "L" -> "\u000A"
                    "N" -> "\u000A"
                    "R" -> "\u000D"
                    "T" -> "\t"
                    else -> {
                        val v = m.group(1)
                        // $nn	Single	Single byte character, where nn is the two digit hexadecimal value of the character
                        // $nnnn	Double	Double byte character, where nnnn is the four digit hexadecimal value of the character
                        v.toInt().toChar().toString()
                    }
                }
                m.appendReplacement(sb, replacement)
            }
            m.appendTail(sb)
            return sb.toString()
        }
    }
}

/**
 * Created by weigl on 25.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class FunctionBlockDataType(var functionBlock: FunctionBlockDeclaration) : AnyDt() {
    override fun repr(obj: Any): String = this.functionBlock!!.name

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    fun asRecord(): RecordType {
        val rt = RecordType(functionBlock.name, functionBlock.scope.variables)
        return rt
    }

    override var name: String
        get() = functionBlock.name
        set(value) {}
}

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 */
class EnumerateType(
    name: String = "ENUM",
    var allowedValues: LinkedHashMap<String, Int> = LinkedHashMap(),
) : AnyDt(name) {
    lateinit var defValue: String

    val bitlength: Int
        get() {
            return ceil(ln(allowedValues.size.toDouble())).toInt()
        }

    constructor(
        name: String,
        allowedValues: MutableList<String>,
        defValue: String = allowedValues[0],
    ) : this(name) {
        allowedValues.forEachIndexed { index, s -> this.allowedValues[s] = index }
        this.defValue = defValue
    }

    constructor(etd: EnumerationTypeDeclaration) : this() {
        name = etd.name
        etd.allowedValues.zip(etd.values).forEach { (a, b) ->
            allowedValues.put(a.text!!.uppercase(Locale.getDefault()), b)
        }
        defValue = etd.allowedValues[0].text.uppercase(Locale.getDefault())
    }

    override fun repr(obj: Any): String = "$name#$obj"

    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)

    fun isAllowedValue(value: String) = this.allowedValues.contains(value)
    operator fun contains(textValue: String) = textValue.uppercase(Locale.getDefault()) in allowedValues

    override fun toString(): String = "ENUM $name"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is EnumerateType) return false

        if (allowedValues != other.allowedValues) return false
        if (defValue != other.defValue) return false

        return true
    }

    override fun hashCode(): Int {
        var result = allowedValues.hashCode()
        result = 31 * result + defValue.hashCode()
        return result
    }

    operator fun get(value: String) = allowedValues[value]
    operator fun get(value: Int) = allowedValues.entries.find { (a, b) -> b == value }?.key

    fun range(start: String, end: String): List<String> {
        val keys = allowedValues.keys.toList()
        val s = keys.indexOf(start)
        val e = keys.indexOf(end)

        if (s < 0) throw IllegalStateException()
        if (e < 0) throw IllegalStateException()

        return keys.subList(s, e + 1)
    }
}

open class AnyInt(var bitLength: kotlin.Int = 0, var isSigned: Boolean = false) : AnyNum() {
    init {
        name = javaClass.getSimpleName().uppercase(Locale.getDefault())
    }

    open val upperBound: BigInteger
        get() =
            if (isSigned) {
                BigInteger.ONE.shiftLeft(bitLength - 1).subtract(BigInteger.ONE)
            } else {
                BigInteger.ONE.shiftLeft(bitLength).subtract(BigInteger.ONE)
            }

    open val lowerBound: BigInteger
        get() {
            if (!isSigned) {
                return BigInteger.ZERO
            } else {
                return BigInteger.ONE.shiftLeft(bitLength - 1).negate()
            }
        }

    constructor(bitLength: kotlin.Int) : this(bitLength, true)

    override fun repr(obj: Any): String = javaClass.getSimpleName().uppercase(Locale.getDefault()) + "#" + obj

    open fun next(): AnyInt? = null

    open fun asUnsigned() = if (isSigned) AnyInt(bitLength, false) else this
    open fun asSigned() = if (isSigned) this else AnyInt(bitLength, true)

    open fun isValid(value: BigInteger): Boolean = value in lowerBound..upperBound

    override fun equals(o: Any?): Boolean {
        if (this === o) return true
        if (o !is AnyInt) return false

        val anyInt = o as AnyInt?

        return if (bitLength != anyInt!!.bitLength) false else isSigned == anyInt.isSigned
    }

    override fun hashCode(): kotlin.Int {
        var result = bitLength
        result = 31 * result + if (isSigned) 1 else 0
        return result
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    override fun toString(): String = name

    companion object {
        fun getDataTypeFor(number: Int, unsigned: Boolean): AnyInt {
            val values: Array<AnyInt>
            if (unsigned) {
                values = arrayOf(USINT, UINT, ULINT, UDINT)
            } else {
                values = arrayOf(SINT, INT, LINT, DINT)
            }

            val bits = Math.ceil(Math.log(number.toDouble()) / Math.log(2.0)).toInt()

            for (candidate in values) {
                if (candidate.bitLength >= bits) {
                    return candidate
                }
            }

            if (bits < 0) {
                return if (unsigned) USINT else SINT
            }

            /*for (AnyInt bit : values)
            if (bit.getBitLength() >= bits)
                return bit;*/

            return if (unsigned) {
                AnyInt(bits, false)
            } else {
                AnyInt(bits, true)
            }
        }
    }
}

object ANY_INT : AnyInt(-1, true)

object UDINT : AnyInt(32, false) {
    override fun next() = ULINT
    override fun asUnsigned() = this
    override fun asSigned() = LINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

object ULINT : AnyInt(64, false) {
    override fun next() = null
    override fun asSigned() = LINT
    override fun asUnsigned() = this
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

object UINT : AnyInt(16, false) {
    override fun next() = UDINT
    override fun asUnsigned() = this
    override fun asSigned() = DINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

object USINT : AnyInt(8, false) {
    override fun asUnsigned() = this
    override fun next() = UINT
    override fun asSigned() = SINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

object INT : AnyInt(16) {
    override fun next() = DINT
    override fun asUnsigned() = UINT
    override fun asSigned() = this
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

object LINT : AnyInt(64) {
    override fun next() = null

    override fun asSigned() = this
    override fun asUnsigned() = ULINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

object SINT : AnyInt(8) {
    override fun next() = INT
    override fun asSigned() = this
    override fun asUnsigned() = USINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

object DINT : AnyInt(32) {
    override fun next() = LINT

    override fun asSigned() = this
    override fun asUnsigned() = UDINT

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class RangeType(
    var bottom: BigInteger = BigInteger.ZERO,
    var top: BigInteger = BigInteger.ZERO,
    var default: BigInteger = bottom,
    var base: AnyInt = INT,
) : AnyInt(base.bitLength, base.isSigned) {

    override val upperBound: BigInteger
        get() = top

    override val lowerBound: BigInteger
        get() = bottom

    override fun repr(obj: Any) = base.repr(obj)
    override fun next() = null
    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
}

// TODO as object
class TimeType : AnyDt("TIME") {

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String {
        val time = obj as TimeData
        val stb = StringTimeBuilder()
        stb.add(time.days.toDouble(), "d")
        stb.add(time.hours.toDouble(), "h")
        stb.add(time.minutes.toDouble(), "m")
        stb.add(time.seconds.toDouble(), "s")
        stb.add(time.milliseconds.toDouble(), "ms")
        return stb.sb.toString()
        /**
         *
         * add.
         *
         * @param value a double.
         * @param unit a [java.lang.String] object.
         */
    }

    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    companion object {
        /** Constant `TIME_TYPE`  */
        val TIME_TYPE = TimeType()
        val LTIME_TYPE = TimeType()
    }
}

internal class StringTimeBuilder {
    var sb = StringBuilder("TIME#")

    fun add(value: Double, unit: String) {
        if (value != 0.0) {
            sb.append(value).append(unit)
        }
    }
}

data class ReferenceDt(val refTo: AnyDt) : AnyDt("REF TO $refTo") {
    override fun repr(obj: Any): String = throw IllegalStateException("No repr for ReferenceDt")

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    companion object {
        val ANY_REF = ReferenceDt(VOID)
    }
}

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class RecordType(override var name: String = ANONYM_DATATYPE, val fields: VariableScope = VariableScope()) : AnyDt(name) {
    fun addField(name: String, dataType: AnyDt) = fields.add(VariableDeclaration(name, dataType))

    override fun repr(obj: Any): String {
        val record = obj as RecordValue
        return record.fieldValues.entries
            .joinToString(", ", "(", ")") { (k, v) ->
                k + ":=" + v.dataType.repr(v.value)
            }
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
}

/**
 * Created by weigl on 01.08.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class PointerType(var of: AnyDt) : AnyDt() {

    /** {@inheritDoc}  */
    override fun toString(): String = of.toString() + "^"

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String = "n/a"

    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)
}
