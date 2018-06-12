package edu.kit.iti.formal.automation.visitors

interface Visitable {
    fun <T> accept(visitor: Visitor<T>): T
}
