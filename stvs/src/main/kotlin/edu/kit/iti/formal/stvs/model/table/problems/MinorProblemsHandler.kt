package edu.kit.iti.formal.stvs.model.table.problems


/**
 * Gets invoked by [InvalidIoVarProblem.tryGetValidIoVariable] if a minor problem is present
 * that does not prevent a variable from being converted to a
 * [edu.kit.iti.formal.stvs.model.common.ValidIoVariable] but should be handled anyways.
 */
fun interface MinorProblemsHandler {
    /**
     * Must implement a handler for minor problems while converting.
     *
     * @param minorProblem The problem which occurred while converting a
     * [edu.kit.iti.formal.stvs.model.common.SpecIoVariable] to a
     * [edu.kit.iti.formal.stvs.model.common.ValidIoVariable]
     */
    fun handle(minorProblem: InvalidIoVarProblem?)
}
