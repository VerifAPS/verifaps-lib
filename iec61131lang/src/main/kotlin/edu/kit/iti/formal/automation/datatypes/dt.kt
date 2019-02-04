package edu.kit.iti.formal.automation.datatypes

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.ast.*
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*


sealed class AnyDt(override var name: String = "ANY") : Identifiable {

    constructor() : this("") {
        name = javaClass.getSimpleName().toUpperCase()
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
    override fun repr(obj: Any): String {
        throw IllegalStateException("No repr for AnyNum")
    }

    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)

    companion object {
        val ANY_NUM: AnyDt = AnyNum()
    }
}

abstract class AnyReal : AnyNum() {
    override fun repr(obj: Any): String {
        val d = obj as BigDecimal
        return name.toUpperCase() + "#" + d
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
        if (obj is Bits)
            if (obj.register > 0)
                return (name.toUpperCase() + "#2#" + java.lang.Long.toBinaryString(obj.register))
        return ""
    }

    object BOOL : AnyBit(1) {
        override fun repr(obj: Any): String {
            if (obj is Bits) {
                if (obj.register > 0)
                    return "TRUE"
            }

            if (obj is Boolean) {
                if (obj)
                    return "TRUE"
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
        val DATATYPES = Arrays.asList(AnyBit.BYTE,
                AnyBit.LWORD, AnyBit.WORD, AnyBit.DWORD, AnyBit.BOOL)
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
            return String.format("DATE#%4d-%2d-%2d",
                    dt.year, dt.month, dt.day)
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
            return visitor.visit(this)
        }
    }

    object TIME_OF_DAY : AnyDate("TIME_OF_DAY") {
        override fun repr(obj: Any): String {
            val dt = obj as TimeofDayData
            return String.format("TOD#%2d:%2d:%2d.%3d",
                    dt.hours, dt.minutes, dt.seconds, dt.millieseconds)
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
            return visitor.visit(this)
        }
    }

    object DATE_AND_TIME : AnyDate("DATE_AND_TIME") {
        override fun repr(obj: Any): String {
            val dt = obj as DateAndTimeData
            return String.format("DT#%4d-%2d-%2d-%2d:%2d:%2d.%3d",
                    dt.year, dt.month, dt.day, dt.hours, dt.minutes, dt.seconds, dt.millieSeconds)
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }
}


class ArrayType(name: String, val fieldType: AnyDt,
                var ranges: MutableList<Range> = ArrayList()) : AnyDt(name) {
    constructor(fieldType: AnyDt, ranges: List<Range>)
            : this(ANONYM_DATATYPE, fieldType, ranges.toMutableList())

    /*
    constructor(arrayTypeDeclaration: ArrayTypeDeclaration) {
        fieldType = arrayTypeDeclaration.baseType
        ranges = arrayTypeDeclaration.ranges
    }
    */

    override fun repr(obj: Any): String {
        val ary = obj as MultiDimArrayValue
        return ary.data.joinToString(",") { fieldType.repr(it.value) }
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    fun allIndices() =
            ranges.map { IntRange(it.startValue, it.stopValue) }
                    .fold(listOf(listOf())) { acc: List<List<Int>>, range: IntRange ->
                        acc.flatMap { l ->
                            range.map { r ->
                                l + r
                            }
                        }
                    }

    fun dimSize(d: Int): Int = ranges[d].stopValue


    override fun reprDecl(): String {
        return if (isAnonym())
            ranges.joinToString(", ", " ARRAY[", "] of ${fieldType.reprDecl()}") {
                "${it.startValue}..${it.stopValue}"
            }
        else
            name
    }
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

    override fun repr(obj: Any) =
            TODO("not implemented") //To change body of created functions use File | Settings | File Templates.

    /* override var fields: Scope
         get() = Scope(OOUtils.getEffectiveScope(clazz).parallelStream()
                 .map<VariableDeclaration>(Function<VariableDeclaration, VariableDeclaration> { it.copy() })
                 .collect<List<VariableDeclaration>, Any>(Collectors.toList()))
         set(value: Scope) {
             super.fields = value
         }
 */

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
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
}


/**
 * Created by weigl on 25.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class FunctionBlockDataType(var functionBlock: FunctionBlockDeclaration) : AnyDt() {
    override fun repr(obj: Any): String {
        return this.functionBlock!!.name
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }

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
class EnumerateType(name: String = "ENUM",
                    var allowedValues: MutableMap<String, Int> = hashMapOf()) : AnyDt(name) {

    val bitlength: Int
        get() {
            return Math.ceil(Math.log(allowedValues.size.toDouble())).toInt()
        }

    lateinit var defValue: String

    constructor(name: String, allowedValues: MutableList<String>,
                defValue: String = allowedValues[0]) : this(name) {
        allowedValues.forEachIndexed { index, s -> this.allowedValues[s] = index }
        this.defValue = defValue
    }

    constructor(etd: EnumerationTypeDeclaration) : this() {
        name = etd.name
        etd.allowedValues.zip(etd.values).forEach { (a, b) ->
            allowedValues.put(a.text!!.toUpperCase(), b)
        }
        defValue = etd.allowedValues[0].text.toUpperCase()
    }

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String {
        return if (name == null)
            obj.toString()
        else
            "$name#$obj"
    }

    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)

    fun isAllowedValue(value: String) = this.allowedValues.contains(value)
    operator fun contains(textValue: String) = textValue.toUpperCase() in allowedValues

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
}

open class AnyInt(var bitLength: kotlin.Int = 0, var isSigned: Boolean = false) : AnyNum() {
    init {
        name = javaClass.getSimpleName().toUpperCase()
    }

    open val upperBound: BigInteger
        get() =
            if (isSigned)
                BigInteger.ONE.shiftLeft(bitLength - 1).subtract(BigInteger.ONE)
            else
                BigInteger.ONE.shiftLeft(bitLength).subtract(BigInteger.ONE)

    open val lowerBound: BigInteger
        get() {
            if (!isSigned)
                return BigInteger.ZERO
            else
                return BigInteger.ONE.shiftLeft(bitLength - 1).negate()
        }

    constructor(bitLength: kotlin.Int) : this(bitLength, true)


    override fun repr(obj: Any): String {
        return javaClass.getSimpleName().toUpperCase() + "#" + obj
    }

    open fun next(): AnyInt? = null

    open fun asUnsigned() = if (isSigned) AnyInt(bitLength, false) else this
    open fun asSigned() = if (isSigned) this else AnyInt(bitLength, true)

    open fun isValid(value: BigInteger): Boolean {
        return value in lowerBound..upperBound
    }

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

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }

    override fun toString(): String = name

    companion object {
        fun getDataTypeFor(number: Int, unsigned: Boolean): AnyInt {
            val values: Array<AnyInt>
            if (unsigned)
                values = arrayOf(USINT, UINT, ULINT, UDINT)
            else
                values = arrayOf(SINT, INT, LINT, DINT)

            val bits = Math.ceil(Math.log(number.toDouble()) / Math.log(2.0)).toInt()

            for (candidate in values) {
                if (candidate.bitLength >= bits)
                    return candidate
            }

            if (bits < 0)
                return if (unsigned) USINT else SINT

            /*for (AnyInt bit : values)
            if (bit.getBitLength() >= bits)
                return bit;*/

            return if (unsigned)
                AnyInt(bits, false)
            else
                AnyInt(bits, true)
        }
    }
}

object ANY_INT : AnyInt(-1, true)

object UDINT : AnyInt(32, false) {
    override fun next() = ULINT
    override fun asUnsigned() = this
    override fun asSigned() = LINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object ULINT : AnyInt(64, false) {
    override fun next() = null
    override fun asSigned() = LINT
    override fun asUnsigned() = this
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object UINT : AnyInt(16, false) {
    override fun next() = UDINT
    override fun asUnsigned() = this
    override fun asSigned() = DINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object USINT : AnyInt(8, false) {
    override fun asUnsigned() = this
    override fun next() = UINT
    override fun asSigned() = SINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object INT : AnyInt(16) {
    override fun next() = DINT
    override fun asUnsigned() = UINT
    override fun asSigned() = this
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object LINT : AnyInt(64) {
    override fun next() = null

    override fun asSigned() = this
    override fun asUnsigned() = ULINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object SINT : AnyInt(8) {
    override fun next() = INT
    override fun asSigned() = this
    override fun asUnsigned() = USINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object DINT : AnyInt(32) {
    override fun next() = LINT

    override fun asSigned() = this
    override fun asUnsigned() = UDINT

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
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
        var base: AnyInt = INT) : AnyInt(base.bitLength, base.isSigned) {

    override val upperBound: BigInteger
        get() = top

    override val lowerBound: BigInteger
        get() = bottom

    override fun repr(obj: Any) = base.repr(obj)
    override fun next() = null
    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
}

//TODO as object
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
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }

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
    override fun repr(obj: Any): String {
        throw IllegalStateException("No repr for ReferenceDt")
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }

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
                    k + "=" + v.dataType.repr(v.value)
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
class PointerType(internal var of: AnyDt) : AnyDt() {

    /** {@inheritDoc}  */
    override fun toString(): String {
        return of.toString() + "^"
    }


    /** {@inheritDoc}  */
    override fun repr(obj: Any): String {
        return "n/a"
    }


    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}
