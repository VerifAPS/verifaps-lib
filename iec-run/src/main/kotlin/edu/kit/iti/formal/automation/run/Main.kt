package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.parser.IEC61131Parser

infix fun String.test(v: String) = v == this

fun main(args: Array<String>) {
    println(1L + 1.0F is Float)
}