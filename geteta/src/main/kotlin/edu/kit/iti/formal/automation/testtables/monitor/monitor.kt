package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton

interface MonitorGeneration {
    fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): String
}

public infix fun SymbolicReference.assignTo(expr: Expression)
        = AssignmentStatement(this, expr)
