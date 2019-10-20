package edu.kit.iti.formal.automation.st.ast

import edu.kit.iti.formal.automation.st.Cloneable
import kotlin.reflect.full.findAnnotation

annotation class PragmaType(val default: String = "")

sealed class Pragma : Cloneable {
    val kind: String
        get() = this.javaClass.getAnnotation(PragmaType::class.java)?.default ?: ""
    abstract override fun clone(): Pragma

    @PragmaType("attribute")
    data class Attribute(var parameters: MutableMap<String, String> = hashMapOf()) : Pragma() {
        var name: String = parameters["#0"]!!
        override fun clone(): Pragma = copy()
    }

}

/**
 *
 */

fun makePragma(type: String, parameters: MutableMap<String, String>): Pragma? {
    Pragma::class.nestedClasses.forEach {
        val a = it.findAnnotation<PragmaType>()?.default
        if (type == a)
            return it.constructors.first().call(parameters) as Pragma
    }
    return null
}