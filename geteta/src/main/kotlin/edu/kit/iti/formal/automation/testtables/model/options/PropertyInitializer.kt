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


import java.beans.BeanInfo
import java.beans.IntrospectionException
import java.beans.Introspector
import java.beans.PropertyDescriptor
import java.lang.reflect.InvocationTargetException
import java.util.Properties

/**
 * Created on 16.12.16
 * @author Alexander Weigl
 * @version 2
 */
class PropertyInitializer(private var value: Any?, private val properties: Properties) {

    fun inject(namespace: String) {
        try {
            val info = Introspector.getBeanInfo(value!!.javaClass)
            for (prop in info.propertyDescriptors) {
                val p = prop.readMethod.getAnnotation(Property::class.java)
                if (p != null) {
                    val path = getPath(namespace, p, prop)
                    if (isSimpleType(prop.propertyType)) {
                        set(path, prop)
                    } else {
                        goDeeper(path, prop)
                    }
                }
            }
        } catch (e: IntrospectionException) {
            e.printStackTrace()
        }

        try {
            val pi = value as InitializableFromProperties?
            pi!!.initialize(namespace, properties)
        } catch (cce: ClassCastException) {
        }

    }

    private fun getPath(namespace: String, p: Property, f: PropertyDescriptor): String {
        return if (p.value.isEmpty()) {
            join(namespace, f.name)
        } else {
            join(namespace, p.value)
        }
    }

    private fun goDeeper(path: String, f: PropertyDescriptor) {
        try {
            val oldValue = value
            value = f.readMethod.invoke(value)
            inject(path)
            value = oldValue
        } catch (e: IllegalAccessException) {
            e.printStackTrace()
        } catch (e: InvocationTargetException) {
            e.printStackTrace()
        }

    }

    private operator fun set(name: String, f: PropertyDescriptor) {
        val type = f.propertyType
        try {
            val `val` = getString(name)
            var s: Any? = null
            if (type.isEnum) {
                for (o in type.enumConstants) {
                    if (o.toString() == `val`) {
                        s = o
                        break
                    }
                }
            } else if (type == Int::class.java)
                s = Integer.parseInt(`val`)
            else if (type == Boolean::class.java)
                s = `val`.equals("true", ignoreCase = true)
            else if (type == String::class.java)
                s = `val`
            else if (type == Long::class.java)
                s = java.lang.Long.parseLong(`val`)

            f.writeMethod.invoke(value, s)
        } catch (npe: NullPointerException) {
            //do nothing
            //npe.printStackTrace();
        } catch (e: InvocationTargetException) {
            e.printStackTrace()
        } catch (e: IllegalAccessException) {
            e.printStackTrace()
        }

    }

    private fun getString(name: String): String {
        return properties.getProperty(name, null) ?: throw NullPointerException()
    }

    private fun join(namespace: String?, name: String): String {
        return if (namespace == null || namespace.isEmpty()) name else arrayOf(namespace, name).joinToString(".")
    }

    private fun isSimpleType(type: Class<*>): Boolean {
        return type.isEnum || type == Int::class.java || type == Boolean::class.java || type == String::class.java || type == Long::class.java
    }

    companion object {
        fun initialize(value: Any, properties: Properties) {
            PropertyInitializer(value, properties).inject("")
        }
    }
}
