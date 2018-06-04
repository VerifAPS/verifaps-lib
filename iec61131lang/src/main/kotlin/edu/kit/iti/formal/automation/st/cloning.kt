package edu.kit.iti.formal.automation.st

import kotlin.reflect.KMutableProperty
import kotlin.reflect.full.memberProperties

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.06.18)
 */
interface Cloneable<T> {
    fun clone(): T {
        val clazz = this::class
        val nObj = clazz.java.newInstance()
        this::class.memberProperties.forEach {
            val prop = it as KMutableProperty<*>
            val value = it.get(this)
            when (value) {
                is Cloneable<*> -> it.setter(nObj, value.clone())
                else -> it.setter(nObj, value)
            }
        }
        return nObj
    }
}
