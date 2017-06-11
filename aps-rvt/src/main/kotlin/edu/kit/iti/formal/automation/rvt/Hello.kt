package edu.kit.iti.formal.automation.rvt

import com.xenomachina.argparser.ArgParser
import edu.kit.iti.formal.automation.rvt.gui.RVTApp
import javafx.application.Application

class MyArgs(parser: ArgParser) {
    val v by parser.flagging(help = "enable verbose mode")
    val widgetName by parser.storing("name of the widget")
    val size by parser.storing("size of the plumbus") { toInt() }
}

fun main(args: Array<String>) {

}

