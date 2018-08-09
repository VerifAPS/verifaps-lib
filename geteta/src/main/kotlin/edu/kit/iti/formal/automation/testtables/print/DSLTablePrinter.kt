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
        stream.printf("table ${gtt.name} {")
        stream.increaseIndent()
        gtt.programVariables.forEach(this::print)
        stream.nl()
        gtt.constraintVariables.forEach(this::print)
        stream.nl()
        print(gtt.properties)
        stream.nl()
        print(gtt.region)
        stream.nl()
        gtt.functions.forEach(this::print)

        stream.decreaseIndent().nl().printf("}")
    }

    fun print(v: ProgramVariable) {
        stream.nl().printf("var ").printf(
                when (v.io) {
                    IoVariableType.INPUT -> "input "
                    IoVariableType.OUTPUT -> "output "
                    IoVariableType.STATE_INPUT -> "state input "
                    IoVariableType.STATE_OUTPUT -> "state output "
                })

        if (v.realName == v.name) {
            stream.printf(v.name).printf(" : ").print(v.dataType)
        } else {
            stream.printf(v.realName).printf(" : ").print(v.dataType).printf(" as ")
                    .printf(v.name)
        }
    }

    fun print(v: ConstraintVariable) {
        stream.nl().printf("gvar ").printf(v.name).printf(" : ").print(v.dataType)
        if (v.constraint != null) {
            stream.printf(" with ").printf(v.constraint!!.text)
        }
    }

    fun print(p: Properties) {
        if (p.isEmpty) return
        stream.nl().printf("options {").increaseIndent()
        p.forEach { t, u ->
            stream.nl().printf("$t = $u")
        }
        stream.nl().decreaseIndent().printf("}")
    }

    fun print(r: TableNode) {
        stream.nl()
        when (r) {
            is Region -> {
                stream.printf("group ${r.id} ")
                print(r.duration)
                stream.printf(" {").increaseIndent()
                r.children.forEach { print(it) }
                stream.decreaseIndent().nl().printf("}")
            }
            is TableRow -> {
                stream.printf("row ${r.id} ")
                print(r.duration)
                stream.printf("{").increaseIndent()
                r.rawFields
                        .filter { (_, u) -> u != null }
                        .forEach { (t, u) -> stream.nl().printf("${t.name}: ${u?.text}") }
                stream.decreaseIndent().nl().printf("}")
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
