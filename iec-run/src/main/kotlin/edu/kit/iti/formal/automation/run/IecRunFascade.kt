package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.st.ast.TopLevelElements

class IecRunFascade(val ast : TopLevelElements) {
    init {
        IEC61131Facade.resolveDataTypes(ast)
    }

    fun executeCode(): TopState {
        val topState = TopState()
        return executeCode(topState)
    }

    fun executeCode(topState : TopState): TopState {
        val runtime = Runtime(topState)
        ast.accept<AnyDt>(runtime)
        return topState
    }
}
