package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.model.table.HybridSpecification

/**
 * This class is notified when a [HybridSpecification] is loaded by
 * [ImporterFacade.importFile].
 */
fun interface ImportHybridSpecificationHandler {
    /**
     * This method needs to be provided by an implementation of
     * `ImportHybridSpecificationHandler`. It is called if a [HybridSpecification] is
     * loaded.
     *
     * @param hybridSpecification HybridSpecification that was loaded
     */
    fun accept(hybridSpecification: HybridSpecification?)
}
