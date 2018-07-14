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
package edu.kit.iti.formal.automation.testtables.io.xmv

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.testtables.io.Report
import edu.kit.iti.formal.automation.testtables.report.Assignment
import edu.kit.iti.formal.automation.testtables.report.Counterexample
import java.io.File
import java.io.IOException
import java.util.regex.Pattern
import java.util.stream.Stream

class NuXMVOutputParser(private val inputLines: Stream<String>) {
    private var ceFound = false
    private var ce: Counterexample = Counterexample()
    internal var invariantHolds: Boolean = false
    private var errorFound: Boolean = false
    private var currentStep: Counterexample.Step = Counterexample.Step()
    private var current: MutableList<Assignment>? = null

    @Throws(IOException::class)
    constructor(input: File) : this(input.readText())

    constructor(content: String) : this(NEWLINE.splitAsStream(content))

    fun run(): Counterexample {
        currentStep = Counterexample.Step()
        current = currentStep.state
        //ce.getStep().add(currentStep);

        inputLines.map { it.trim({ it <= ' ' }) }
                .forEach { handle(it) }

        if (ceFound) {
            Report.setErrorLevel("not-verified")
            Report.setCounterExample(ce)
        } else if (invariantHolds)
            Report.setErrorLevel("verified")
        else if (errorFound)
            Report.setErrorLevel("nuxmv-error")
        else
            Report.setErrorLevel("unknown")

        return ce
    }

    private fun handle(line: String) {
        if (line.contains("error")
                || line.contains("TYPE ERROR")
                || line.contains("undefined")) {
            Report.fatal("NUXMV error: %s", line)
            errorFound = true
        } else {
            if (ceFound) {

                if (INPUT_MARKER.matcher(line).matches()) {
                    current = currentStep.input
                    return
                }

                val m = SPLIT_MARKER.matcher(line)
                if (m.matches()) {
                    val step = Integer.parseInt(m.group(2))
                    currentStep = Counterexample.Step()
                    ce.step.add(currentStep)
                    current = currentStep!!.state
                    return
                }

                assignment(line)
            } else {
                ceFound = SKIP_MARKER.matcher(line).matches()
                invariantHolds = invariantHolds || line.contains("is true")
            }
        }

    }

    private fun assignment(line: String) {
        val m = ASSIGNMENT_SEPERATOR.matcher(line)
        if (m.matches()) {
            val a = Assignment()
            a.name = m.group(1).trim { it <= ' ' }
            a.value = m.group(2).trim { it <= ' ' }
            current!!.add(a)
        }
    }

    companion object {
        val SKIP_MARKER = Pattern.compile("Trace Type: Counterexample")
        val SPLIT_MARKER = Pattern.compile("-> State: (\\d+).(\\d+) <-")
        val INPUT_MARKER = Pattern.compile("-> Input: (\\d+).(\\d+) <-")
        val NEWLINE = Pattern.compile("\n")
        internal val ASSIGNMENT_SEPERATOR = Pattern.compile("(.*)\\s*=\\s*(.*)")
    }
}
