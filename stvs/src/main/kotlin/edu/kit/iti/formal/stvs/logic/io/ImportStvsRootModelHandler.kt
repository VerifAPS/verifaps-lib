package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.model.StvsRootModel

/**
 * An ImportStvsRootModelHandler is notified when a [StvsRootModel] is loaded by
 * [ImporterFacade.importFile].
 */
fun interface ImportStvsRootModelHandler {
    /**
     * This method needs to be provided by an implementation of `ImportStvsRootModelHandler`. It
     * is called if a [StvsRootModel] is loaded.
     *
     * @param model StvsRootModel that was loaded
     */
    fun accept(model: StvsRootModel)
}
