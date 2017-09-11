package edu.kit.iti.formal.automation.run

import org.junit.Assert.assertEquals
import org.junit.Test
import java.util.*

class RuntimeTest {

    @Test
    fun testIfStatement() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.testIfStatement.st"))
        val topState = TopState()
        ast.accept<Any>(Runtime(topState))
        assertEquals(arrayListOf(
                "number" to Optional.of(300),
                "n2" to Optional.of(4),
                "active" to Optional.of(true)).toString(),
                topState.map { it.key to it.value.map { it.value } }.toString())
    }

    @Test
    fun testVariableReference() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.testVariableReference.st"))
        val topState = TopState()
        ast.accept<Any>(Runtime(topState))
        print("result of execution: $topState")
        assertEquals(
                HashSet(listOf(
                        "b2" to Optional.of(true),
                        "number" to Optional.of(-19),
                        "n2" to Optional.of(-17),
                        "b" to Optional.of(false),
                        "n3" to Optional.of(4),
                        "n4" to Optional.empty()
                )).toString(),
                HashSet(topState.map { it.key to it.value.map { it.value } }).toString()
        )

    }

    @Test
    fun advancedTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.advancedTest.st"))
        val topState = TopState()
        ast.accept<Any>(Runtime(topState))
        println("final state:")
        topState.forEach {
            println(it)
        }
    }

    @Test
    fun elevatorTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.elevatorTest.st"))
        val topState = TopState()
        ast.accept<Any>(Runtime(topState))
        println("final state:")
        topState.forEach {
            println(it)
        }
    }
}