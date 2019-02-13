package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.datatypes.values.FALSE
import edu.kit.iti.formal.automation.datatypes.values.TRUE
import edu.kit.iti.formal.automation.datatypes.values.VAnyEnum
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class RuntimeTest {
    @Test
    fun testIfStatement() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.testIfStatement.st"))
        println(ast.toString())
        val state = ExecutionFacade.execute(ast)
        assertEquals(hashMapOf(
                "number" to VAnyInt(INT, 300),
                "n2" to VAnyInt(INT, 4),
                "active" to TRUE),
                state)
    }

    @Test
    fun testVariableReference() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.testVariableReference.st"))
        val state = ExecutionFacade.execute(ast)
        print("result of execution: $state")
        assertEquals(hashMapOf(
                "b2" to TRUE,
                "n8" to TRUE,
                "n9" to TRUE,
                "number" to VAnyInt(INT, -19),
                "n2" to VAnyInt(INT, -1),
                "n10" to FALSE,
                "b" to FALSE,
                "n3" to VAnyInt(INT, 4),
                "n4" to VAnyInt(INT, 0),
                "n5" to VAnyInt(INT, 6),
                "n6" to VAnyInt(INT, 6),
                "n7" to VAnyInt(INT, -1)
        ),
                state)
    }

    @Test
    fun advancedTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.advancedTest.st"))
        val state = ExecutionFacade.execute(ast)
        println("final state:")
        state.forEach {
            println(it)
        }
    }

    @Test
    fun elevatorTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.elevatorTest.st"))
        val ec = ExecutionFacade.createExecutionContext(ast)
        val input1 = State()
        input1["ButtonPressed"] = TRUE
        ec.executeCycle(input = input1)
        println("1st state:")
        ec.lastState.forEach {
            println(it)
        }

        val enumMotorState = ec.entryPoint.scope.resolveDataType("MOTOR_STATE") as EnumerateType
        val enumDoorState = ec.entryPoint.scope.resolveDataType("DOOR_STATE") as EnumerateType

        assertEquals(hashMapOf("RequestedPos" to VAnyInt(INT, 5),
                "CurrentPos" to VAnyInt(INT, 3),
                "Motor" to VAnyEnum(enumMotorState, "GoUp"),
                "ButtonPressed" to TRUE,
                "Door" to VAnyEnum(enumDoorState, "Closed")
        ), ec.lastState)

        val input2 = State()
        input2["CurrentPos"] = VAnyInt(UINT, 5)
        ec.executeCycle(input = input2)
        println("2nd state:")
        ec.lastState.forEach { println(it) }

        assertEquals(hashMapOf(
                "RequestedPos" to VAnyInt(INT, 5),
                "CurrentPos" to VAnyInt(UINT, 5),
                "Motor" to VAnyEnum(enumMotorState, "Stationary"),
                "ButtonPressed" to TRUE,
                "Door" to VAnyEnum(enumDoorState, "Open")
        ), ec.lastState)
    }

    @Test
    fun forLoopTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.forLoopTest.st"))
        val state = ExecutionFacade.execute(ast)
        println("final state:")
        state.forEach {
            println(it)
        }
        assertEquals(VAnyInt(INT, 32), state["Var1"]!!)
    }

    @Test
    fun whileLoopTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.whileLoopTest.st"))
        val state = ExecutionFacade.execute(ast)
        println("final state:")
        state.forEach {
            println(it)
        }
        assertEquals(VAnyInt(INT, 32), state["Var1"])
        assertEquals(VAnyInt(INT, 0), state["counter"])
    }

    @Test
    fun repeatLoopTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.repeatLoopTest.st"))
        val state = ExecutionFacade.execute(ast)
        println("final state:")
        state.forEach {
            println(it)
        }
        assertEquals(VAnyInt(INT, 32), state["Var1"])
        assertEquals(VAnyInt(INT, 0), state["counter"])
    }

    @Test
    fun functionBlockTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.functionBlockTest.st"))
        //val state = ExecutionFacade.execute(ast)
        val exec = ExecutionFacade.createExecutionContext(ast)
        exec.lastState.forEach { println(it) }
        exec.executeCycle()
        exec.lastState.forEach { println(it) }
    }

    @Test
    fun structTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.structTest.st"))
        val state = ExecutionFacade.execute(ast)
        state.forEach { println(it) }
    }

    @Test
    fun functionTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.functionTest.st"))
        val state = ExecutionFacade.execute(ast)
        state.forEach { println(it) }
        assertEquals(VAnyInt(INT, -162), state["Var1"])
        assertEquals(VAnyInt(INT, 7), state["x"])
        assertEquals(VAnyInt(INT, 8), state["y"])
    }

    @Test
    fun cyclesTest() {
        val ast = IEC61131Facade.file(this.javaClass.getResourceAsStream("runtimeTest.cycles.st"))
        val exec = ExecutionFacade.createExecutionContext(ast)
        var counter: Long = 0

        println(exec.lastState)
        assertEquals(VAnyInt(INT, counter), exec.lastState["counter"])

        val execTime = arrayListOf<Long>()
        for (i in 1..1000.toLong()) {
            val startTime = System.nanoTime()
            val state = exec.executeCycle(
                    "I" to VAnyInt(INT, i))
            val stopTime = System.nanoTime()
            execTime.add(stopTime - startTime)

            counter = if (counter + i > 1000) 0 else counter + i
            assertEquals(VAnyInt(INT, counter), state["counter"])
        }

        println("Average cycle time: ${execTime.average()/1000/1000} ms")
    }
}
