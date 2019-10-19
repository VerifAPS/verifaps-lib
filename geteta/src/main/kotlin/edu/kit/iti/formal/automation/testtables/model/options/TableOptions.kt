/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.model.options

import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique
import kotlin.properties.ReadWriteProperty
import kotlin.reflect.KProperty

interface StringConverter<T> {
    fun from(s: String): T
    fun to(t: T): String
}

class AnyConverter<T>(val _to: (T) -> String, val _from: (String) -> T) : StringConverter<T> {
    override fun from(s: String) = _from(s)
    override fun to(t: T): String = _to(t)
}


object IntConverter : StringConverter<Int> {
    override fun from(s: String) = s.toInt()
    override fun to(t: Int): String = t.toString()
}

object strConverter : StringConverter<String> {
    override fun from(s: String) = s
    override fun to(t: String): String = t
}

object booleanConverter : StringConverter<Boolean> {
    override fun from(s: String) = "true".equals(s, true)
    override fun to(t: Boolean): String = t.toString()
}

open class Options(
        val namespace: String,
        val properties: MutableMap<String, String>) {

    inner class MapperN<T>(private val default: T?=null,
                          private val conv: StringConverter<T>) {
        operator fun setValue(obj: Options, property: KProperty<*>, value: T?) {
            val n = namespace + (if (namespace.isBlank()) "" else ".") + property.name
            if(value==null) obj.properties.remove(n)
            else obj.properties[n] = conv.to(value)
        }

        operator fun getValue(obj: Options, property: KProperty<*>): T? {
            val n = namespace + (if (namespace.isBlank()) "" else ".") + property.name
            return obj.properties[n]?.let { conv.from(it) } ?: default
        }
    }

    inner class Mapper<T>(private val default: T,
                          private val conv: StringConverter<T>) {
        operator fun setValue(obj: Options, property: KProperty<*>, value: T) {
            val n = namespace + (if (namespace.isBlank()) "" else ".") + property.name
            obj.properties[n] = conv.to(value)
        }

        operator fun getValue(obj: Options, property: KProperty<*>): T {
            val n = namespace + (if (namespace.isBlank()) "" else ".") + property.name
            return obj.properties[n]?.let { conv.from(it) } ?: default
        }
    }

    protected val integer = MapperN(null, IntConverter)
    protected val string = MapperN(null, strConverter)
    protected val boolean = MapperN(null, booleanConverter)
    protected fun integer(default: Int) = Mapper(default, IntConverter)
    protected fun string(default: String) = Mapper(default, strConverter)
    protected fun boolean(default:Boolean) = Mapper(default, booleanConverter)

    protected fun <T> any(default: T,
                          to: (T) -> String,
                          from: (String) -> T) = Mapper(default, AnyConverter(to, from))
}



/**
 * Created by weigl on 16.12.16.
 */
class TableOptions(properties: MutableMap<String, String>) : Options("", properties) {
    var mode: Mode  by any(Mode.CONFORMANCE, Mode::toString, Mode::valueOf)

    val verificationTechnique: VerificationTechnique
            by properties.convert(VerificationTechnique.IC3) { VerificationTechnique.valueOf(it) }

    var cycles: ConcreteTableOptions = ConcreteTableOptions(properties)
    var dataTypeOptions = DataTypeOptions(properties)
    var relational: Boolean = false

    val monitor = MonitorOptions(properties)
}

class MonitorOptions(properties: MutableMap<String, String>) : Options("monitor", properties) {
    val dynamic by boolean(false)
    val trigger by string
}

fun <R, T> Map<String, String>.convert(default: T, func: (String) -> T): ReadWriteProperty<R, T> {
    return object : ReadWriteProperty<R, T> {
        var overwritten: T? = null
        override fun setValue(thisRef: R, property: KProperty<*>, value: T) {
            overwritten = value
        }

        override fun getValue(thisRef: R, property: KProperty<*>): T {
            if (overwritten != null) return overwritten!!
            val v = this@convert[property.name]
            return if (v == null) return default
            else func(v)
        }
    }
}

