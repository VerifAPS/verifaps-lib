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
package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.testtables.exception.ProgramAbortionException
import edu.kit.iti.formal.automation.testtables.report.Assignment
import edu.kit.iti.formal.automation.testtables.report.Counterexample
import edu.kit.iti.formal.automation.testtables.report.Message
import edu.kit.iti.formal.automation.testtables.report.ObjectFactory
import javax.xml.bind.JAXBContext
import javax.xml.bind.JAXBException
import javax.xml.bind.Marshaller

/**
 * @author Alexander Weigl
 * @version 1 (11.12.16)
 */
@Deprecated("""....""")
object Report {
    var XML_MODE = false
    internal var START_TIME = System.currentTimeMillis()
    var message: Message = Message()

    init {
        clear()
    }

    fun clear() {
        message = Message()
        message.log = Message.Log()
        message.returncode = "unknown"
    }

    fun debug(msg: String, vararg args: Any?) {
        print("debug", msg, *args)
    }

    fun info(msg: String, vararg args: Any?) {
        print("info", msg, *args)
    }

    fun warn(msg: String, vararg args: Any?) {
        print("warn", msg, *args)
    }

    fun error(msg: String?, vararg args: Any?) {
        print("error", msg, *args)
    }

    fun fatal(msg: String?, vararg args: Any?) {
        print("fatal", msg, *args)
        setErrorLevel("fatal-error")
    }

    fun abort() {
        throw ProgramAbortionException()
    }

    private fun print(level: String, fmt: String?, vararg args: Any?) {
        if (fmt == null) {
            return //            throw new IllegalArgumentException("fmt is null");
        }
        val e = Message.Log.Entry()
        e.level = level
        e.time = (System.currentTimeMillis() - START_TIME).toInt()
        e.value = String.format(fmt, *args)
        message.log.entry.add(e)
    }

    fun setErrorLevel(s: String) {
        message.returncode = s
    }

    fun close() {
        if (!XML_MODE) {
            for (e in message.log.entry) {
                System.out.printf("[%5d] (%5s): %s%n", e.time, e.level, e.value)
            }

            var i = 0
            if (message.counterexample != null) {
                for (step in message.counterexample
                        .trace.step) {
                    System.out.format("STEP %d %n", i++)
                    step.input.forEach(Report.print("INPUT > "))
                    step.state.forEach(Report.print("STATE > "))
                    println()
                }

                if (message.counterexample.rowMappings != null) {
                    message.counterexample.rowMappings.rowMap
                            .forEach { rm -> println("ROWMAP > " + rm) }
                }
            }
            println("STATUS: " + message.returncode)
        } else {
            try {
                val jaxbContext = JAXBContext.newInstance(ObjectFactory::class.java)
                val m = jaxbContext.createMarshaller()
                m.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, java.lang.Boolean.TRUE)
                m.marshal(message, System.out)
            } catch (e: JAXBException) {
                e.printStackTrace()
            }

        }

    }

    private fun print(suffix: String): (Assignment) -> Unit {
        return { assignment: Assignment ->
            println("$suffix${assignment.name} = ${assignment.value}")
        }
    }

    fun setCounterExample(counterExample: Counterexample) {
        if (message.counterexample == null) {
            message.counterexample = Message.Counterexample()
        }
        message.counterexample.trace = counterExample
    }
}
