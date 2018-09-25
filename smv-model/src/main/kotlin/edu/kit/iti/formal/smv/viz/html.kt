package edu.kit.iti.formal.smv.viz

import edu.kit.iti.formal.smv.CounterExample
import kotlinx.html.*
import kotlinx.html.stream.appendHTML
import java.io.StringWriter
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (26.09.18)
 */
class SingleTraceHtmlPage(val counterExample: CounterExample) {
    val inputNames = counterExample.inputVariables.toSortedSet()
    val stateNames: SortedSet<String> by lazy {
        val names = counterExample.states[0].keys.toSortedSet()
        names.removeAll(inputNames)
        names
    }

    val stylesheets: MutableList<String> = arrayListOf()
    val scripts: MutableList<String> = arrayListOf()

    fun render(): String {
        val sw = StringWriter()
        sw.appendHTML().html {
            printHeader(this)
            body {
                div("root") {
                    div("helper") {
                        h2 { +"Variables" }
                        div {
                            ul {
                                inputNames.forEach { createCheckLIChkBox(this@ul, it, "input") }
                                stateNames.forEach { createCheckLIChkBox(this@ul, it, "state") }
                            }
                        }
                    }
                    div("content") {
                        for (step in 0 until counterExample.stateSize) {
                            div("step step-$step") {
                                h2 { +"Step ${step + 1}" }
                                table {
                                    inputNames.forEach { printInput(this@table, step, it) }
                                    tr("separator")
                                    stateNames.forEach { printState(this@table, step, it) }
                                }
                            }
                        }
                    }
                }
            }
        }
        return sw.toString()
    }

    private fun createCheckLIChkBox(ul: UL, label: String, classes: String? = null) {
        ul.li {
            label(classes) {
                checkBoxCommand {
                    checked = true
                }
                +label
            }
        }
    }

    private fun printState(table: TABLE, step: Int, name: String) = printCell(table, step, name, "state")

    private fun printInput(table: TABLE, step: Int, name: String) = printCell(table, step, name, "input")

    private fun printCell(table: TABLE, step: Int, name: String, classes: String) {
        val value = counterExample.get(step, name) ?: "n/a"
        table.tr(classes) {
            td("variable-name") { +name }
            td("variable-value") { +value }
        }
    }


    private fun printHeader(html: HTML) {
        html.head {
            stylesheets.forEach {
                link(it, "stylesheet", "text/css")
            }

            scripts.forEach {
                script("javascript", it) {}
            }
        }
    }
}
}