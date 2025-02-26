package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.automation.analysis.toHuman
import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SList

/**
 * Represents sets of constraints and definitions.
 *
 * @author Carsten Csiky
 */
data class SmtModel(
    val globalConstraints: MutableList<SExpr> = arrayListOf(),
    val variableDefinitions: MutableList<SExpr> = arrayListOf()
) {
    /**
     * Adds all constraints and definitions of `other` to this object.
     *
     * @param other object from which the constraints/definitions should be taken
     * @return this (now with added constraints/definitions)
     */
    fun combine(other: SmtModel): SmtModel {
        globalConstraints.addAll(other.globalConstraints)
        variableDefinitions.addAll(other.variableDefinitions)
        return this
    }

    fun toSexpr(): List<SExpr> {
        val seq = ArrayList(variableDefinitions)

        globalConstraints.forEach {
            seq.add(SList("assert", it))
        }
        return seq
    }

    /**
     * Converts all definitions to text compatible with smt definitions.
     *
     * @return definitions as string
     */
    fun headerToText(): String {
        return distinctVariableDefinitions.joinToString("\n") {
            it.toHuman()
        }
    }

    /**
     * Converts all global constraints to text compatible with smt.
     *
     * @return constraints as string
     */
    fun globalConstraintsToText(): String {
        return globalConstraints
            .joinToString(" \n ") { SList("assert", it).toString() }
    }

    fun toText(): String {
        return "${headerToText()}\n${globalConstraintsToText()}"
    }

    fun addGlobalConstraint(c: SExpr): SmtModel {
        this.globalConstraints.add(c)
        return this
    }

    fun addHeaderDefinition(c: SExpr): SmtModel {
        this.variableDefinitions.add(c)
        return this
    }

    val distinctVariableDefinitions: Set<SExpr>
        get() = LinkedHashSet(variableDefinitions)
}
