package edu.kit.iti.formal.automation.st

import kotlin.reflect.KMutableProperty
import kotlin.reflect.full.memberProperties

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.06.18)
 */
interface Cloneable<T> {
    @Suppress("UNCHECKED_CAST")
    fun clone(): T {
        val clazz = this::class
        val nObj = clazz.java.newInstance()
        this::class.memberProperties.forEach {
            val prop = it as KMutableProperty<*>
            val value = it.getter.call(this)
            when (value) {
                is Cloneable<*> -> it.setter.call(nObj, value.clone())
                is List<*> -> {
                    val nVal = ArrayList(value)
                    it.setter.call(nObj, this)
                }
                else -> it.setter.call(nObj, value)
            }
        }
        return nObj as T
    }
}
