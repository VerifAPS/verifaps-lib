package edu.kit.iti.formal.automation.run

import com.sun.istack.internal.logging.Logger
import edu.kit.iti.formal.automation.IEC61131Facade
import mu.KLogging
import mu.KotlinLogging
import org.junit.Assert.assertEquals
import org.junit.Before
import org.junit.Test
import java.math.BigInteger
import java.util.*
class RuntimeTest {
    @Before
    fun setUp() {
        System.setProperty(org.slf4j.impl.SimpleLogger.DEFAULT_LOG_LEVEL_KEY, "TRACE");
    }

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

    @Test
    fun forLoopTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.forLoopTest.st"))
        val topState = TopState()
        ast.accept<Any>(Runtime(topState))
        println("final state:")
        topState.forEach {
            println(it)
        }
        assertEquals(BigInteger.valueOf(32), topState["Var1"]!!.get().value)
    }

    @Test
    fun whileLoopTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.whileLoopTest.st"))
        val topState = TopState()
        ast.accept<Any>(Runtime(topState))
        println("final state:")
        topState.forEach {
            println(it)
        }
        assertEquals(BigInteger.valueOf(32), topState["Var1"]!!.get().value)
        assertEquals(BigInteger.valueOf(0), topState["counter"]!!.get().value)
    }

    @Test
    fun repeatLoopTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.repeatLoopTest.st"))
        val topState = TopState()
        ast.accept<Any>(Runtime(topState))
        println("final state:")
        topState.forEach {
            println(it)
        }
        assertEquals(BigInteger.valueOf(32), topState["Var1"]!!.get().value)
        assertEquals(BigInteger.valueOf(0), topState["counter"]!!.get().value)
    }

    @Test
    fun functionBlockTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.functionBlockTest.st"))
        val topState = TopState()
        IEC61131Facade.resolveDataTypes(ast)
        val runtime = Runtime(topState)
        ast.accept<Any>(runtime)
        println("final state:")

        topState.forEach {
            println(it)
        }
    }

    @Test
    fun structTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.structTest.st"))
        val topState = TopState()
        IEC61131Facade.resolveDataTypes(ast)

        val runtime = Runtime(topState)
        ast.accept<Any>(runtime)

        println("final state")
        topState.forEach {

            println(it)
        }
    }

    @Test
    fun functionTest() {
        val ast = getAst(this.javaClass.getResource("runtimeTest.functionTest.st"))
        val topState = TopState()
        val runtime = Runtime(topState, Stack())
        ast.accept<Any>(runtime)
        println("final state:")

        assertEquals(BigInteger.valueOf(-162), topState["Var1"]!!.get().value)
        assertEquals(BigInteger.valueOf(7), topState["x"]!!.get().value)
        assertEquals(BigInteger.valueOf(8), topState["y"]!!.get().value)
    }

}