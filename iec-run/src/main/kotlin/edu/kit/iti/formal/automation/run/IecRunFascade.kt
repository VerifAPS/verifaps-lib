package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.TopLevelElements

class IecRunFascade(val ast : TopLevelElements) {
    val topState = TopState()
    val runtime = Runtime(topState)

    init {
        IEC61131Facade.resolveDataTypes(ast)
    }

    fun execute(): TopState {
        ast.accept<Any>(runtime)
        return topState
    }
}