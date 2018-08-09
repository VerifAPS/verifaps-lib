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


/**
 * Created by weigl on 16.12.16.
 */
class TableOptions(val properties: MutableMap<String, String>) {
    var mode: Mode
            by properties.convert(Mode.CONFORMANCE) { Mode.valueOf(it) }

    val verificationTechnique: VerificationTechnique
            by properties.convert(VerificationTechnique.IC3) { VerificationTechnique.valueOf(it) }

    var cycles: ConcreteTableOptions = ConcreteTableOptions(properties)
    var dataTypeOptions = DataTypeOptions(properties)
    var relational: Boolean = false
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

