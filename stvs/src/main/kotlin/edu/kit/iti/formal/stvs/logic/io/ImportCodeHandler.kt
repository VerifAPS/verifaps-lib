package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.model.code.Code

/**
 * An `ImportCodeHandler` is notified when [Code] is loaded by
 * [ImporterFacade.ImportFormat.importFile].
 */
fun interface ImportCodeHandler {
    /**
     * This method needs to be provided by an implementation of `ImportCodeHandler`. It is
     * called if [Code] is loaded.
     *
     * @param code Code that was loaded
     */
    fun accept(code: Code)
}
