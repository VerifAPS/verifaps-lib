package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.smv.CounterExample
import javax.swing.text.Position

typealias LineMap = HashMap<Int, Pair<String, Position>>

class TraceToProgram(val cex: CounterExample,
                     val lineMap : LineMap,
                     val program : ProgramDeclaration) {

}