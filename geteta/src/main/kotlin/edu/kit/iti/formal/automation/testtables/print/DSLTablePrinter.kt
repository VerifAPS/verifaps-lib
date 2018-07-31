package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.automation.testtables.model.*
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.07.18)
 */
class DSLTablePrinter(val stream: CodeWriter) {
    fun print(gtt: GeneralizedTestTable) {
        stream.append("table ${gtt.name} {")
        stream.increaseIndent()
        gtt.ioVariables.forEach(this::print)
        stream.nl()
        gtt.constraintVariables.forEach(this::print)
        stream.nl()
        print(gtt.properties)
        stream.nl()
        print(gtt.region)
        stream.nl()
        gtt.functions.forEach(this::print)

        stream.decreaseIndent().nl().append("}")
    }

    fun print(v: IoVariable) {
        stream.nl().append("var ").append(
                when (v.io) {
                    IoVariableType.INPUT -> "input "
                    IoVariableType.OUTPUT -> "output "
                    IoVariableType.STATE_INPUT -> "state input "
                    IoVariableType.STATE_OUTPUT -> "state output "
                })

        if (v.realName == v.name) {
            stream.append(v.name).append(" : ").append(v.dataType)
        } else {
            stream.append(v.realName).append(" : ").append(v.dataType).append(" as ")
                    .append(v.name)
        }
    }

    fun print(v: ConstraintVariable) {
        stream.nl().append("gvar ").append(v.name).append(" : ").append(v.dataType)
        if (v.constraint != null) {
            stream.append(" with ").append(v.constraint!!.text)
        }
    }

    fun print(p: Properties) {
        if (p.isEmpty) return
        stream.nl().append("options {").increaseIndent()
        p.forEach { t, u ->
            stream.nl().append("$t = $u")
        }
        stream.nl().decreaseIndent().append("}")
    }

    fun print(r: TableNode) {
        stream.nl()
        when (r) {
            is Region -> {
                stream.append("group ${r.id} ")
                print(r.duration)
                stream.append(" {").increaseIndent()
                r.children.forEach { print(it) }
                stream.decreaseIndent().nl().append("}")
            }
            is State -> {
                stream.append("row ${r.id} ")
                print(r.duration)
                stream.append("{").increaseIndent()
                r.rawFields
                        .filter { (_, u) -> u != null }
                        .forEach { (t, u) -> stream.nl().append("${t.name}: ${u?.text}") }
                stream.decreaseIndent().nl().append("}")
            }
        }
    }

    fun print(d: Duration) = stream.write(when (d) {
        is Duration.Omega -> "omega"
        is Duration.ClosedInterval -> "[${d.lower}, ${d.upper}]" + (if (d.pflag) ">>" else "")
        is Duration.OpenInterval -> ">= ${d.lower}" + (if (d.pflag) ">>" else "")
    })

    fun print(fs: FunctionDeclaration) {
        val stp = StructuredTextPrinter()
        stp.sb = stream
        fs.accept(stp)
    }
}
