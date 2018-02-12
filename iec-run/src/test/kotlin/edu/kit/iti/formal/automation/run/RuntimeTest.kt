package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.values.Values
import org.junit.Assert.assertEquals
import org.junit.Before
import org.junit.Test
import java.math.BigInteger
import java.util.*
class RuntimeTest {
    @Before
    fun setUp() {
        System.setProperty(org.slf4j.impl.SimpleLogger.DEFAULT_LOG_LEVEL_KEY, "TRACE");

/*-
 * #%L
 * iec-run
 * %%
 * Copyright (C) 2018 Alexander Weigl
 * %%
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
 * #L%
 */
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
                        "n8" to Optional.of(true),
                        "n9" to Optional.of(true),
                        "number" to Optional.of(-19),
                        "n2" to Optional.of(-1),
                        "n10" to Optional.of(false),
                        "b" to Optional.of(false),
                        "n3" to Optional.of(4),
                        "n4" to Optional.empty(),
                        "n5" to Optional.of(6),
                        "n6" to Optional.of(6),
                        "n7" to Optional.of(-1)
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
        val exec = IecRunFascade(ast)

        topState["ButtonPressed"] = Optional.of(Values.VBool(AnyBit.BOOL, true) as ExpressionValue)
        exec.executeCode(topState)

        println("1st state:")
        topState.forEach {
            println(it)
        }

        assertEquals(
                HashSet(listOf(
                        "RequestedPos" to Optional.of(5),
                        "CurrentPos" to Optional.of(3),
                        "Motor" to Optional.of("GoUp"),
                        "ButtonPressed" to Optional.of(true),
                        "Door" to Optional.of("Closed")
                )).toString(),
                HashSet(topState.map { it.key to it.value.map { it.value } }).toString()
        )



        topState["CurrentPos"] = Optional.of(Values.VAnyInt(AnyInt.getDataTypeFor(5, false), BigInteger.valueOf(5)) as ExpressionValue)

        exec.executeCode(topState)

        println("2nd state:")
        topState.forEach {
            println(it)
        }

        assertEquals(
                HashSet(listOf(
                        "RequestedPos" to Optional.of(5),
                        "CurrentPos" to Optional.of(5),
                        "Motor" to Optional.of("Stationary"),
                        "ButtonPressed" to Optional.of(true),
                        "Door" to Optional.of("Open")
                )).toString(),
                HashSet(topState.map { it.key to it.value.map { it.value } }).toString()
        )


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
        val exec = IecRunFascade(ast)
        exec.executeCode()

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
