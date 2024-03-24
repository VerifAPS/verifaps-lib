package edu.kit.iti.formal.stvs.logic.specification.smtlib

import de.tudresden.inf.lat.jsexp.Sexp
import java.util.*
import java.util.function.Consumer
import java.util.stream.Collectors

/**
 * Represents sets of constraints and definitions.
 *
 * @author Carsten Csiky
 */
class SmtModel : SExpression {
    @JvmField
    val globalConstraints: MutableList<SExpression?>?
    @JvmField
    val variableDefinitions: MutableList<SExpression?>?

    /**
     * Creates an instance with preset definitions/constraints. both lists should be modifiable
     *
     * @param globalConstraints list of global constraints
     * @param variableDefinitions list of variable definitions
     */
    constructor(globalConstraints: MutableList<SExpression?>?, variableDefinitions: MutableList<SExpression?>?) {
        this.globalConstraints = globalConstraints
        this.variableDefinitions = variableDefinitions
    }

    /**
     * Creates an instance with empty sets.
     */
    constructor() {
        this.globalConstraints = ArrayList()
        this.variableDefinitions = ArrayList()
    }

    /**
     * Adds all constraints and definitions of `other` to this object.
     *
     * @param other object from which the constraints/definitions should be taken
     * @return this (now with added constraints/definitions)
     */
    fun combine(other: SmtModel?): SmtModel {
        addGlobalConstrains(other!!.globalConstraints)
        addHeaderDefinitions(other.variableDefinitions)
        return this
    }

    override val isAtom: Boolean
        get() = false

    override fun toSexpr(): Sexp? {
        val equivalentSList = SList().addAll(
            variableDefinitions
        )
        globalConstraints?.forEach(Consumer { constraint: SExpression? -> equivalentSList.addAll(SList("assert", constraint)) })
        return equivalentSList!!.toSexpr()
    }

    /**
     * Converts all definitions to text compatible with smt definitions.
     *
     * @return definitions as string
     */
    fun headerToText(): String {
        return distinctVariableDefinitions.stream().map { obj: SExpression? -> obj!!.toText() }
            .collect(Collectors.joining(" \n "))
    }

    /**
     * Converts all global constraints to text compatible with smt.
     *
     * @return constraints as string
     */
    fun globalConstraintsToText(): String {
        return globalConstraints!!.stream().map { constr: SExpression? -> SList("assert", constr) }
            .map { obj: SList -> obj.toText() }.collect(Collectors.joining(" \n "))
    }

    override fun toText(): String? {
        return """${headerToText()} 
 ${globalConstraintsToText()}"""
    }

    fun addGlobalConstrains(vararg globalConstraint: SExpression?): SmtModel {
        return addGlobalConstrains(Arrays.asList(*globalConstraint))
    }

    fun addGlobalConstrains(globalConstraints: Collection<SExpression?>?): SmtModel {
        this.globalConstraints!!.addAll(globalConstraints!!)
        return this
    }

    fun addHeaderDefinitions(vararg variableDefinition: SExpression?): SmtModel {
        return addHeaderDefinitions(Arrays.asList(*variableDefinition))
    }

    fun addHeaderDefinitions(variableDefinitions: Collection<SExpression?>?): SmtModel {
        this.variableDefinitions!!.addAll(variableDefinitions!!)
        return this
    }

    val distinctVariableDefinitions: Set<SExpression?>
        get() = LinkedHashSet(variableDefinitions)

    override fun toString(): String {
        return ("SmtModel{\n" + "\tglobalConstraints=\n\t\t"
                + globalConstraints!!.stream().map { obj: SExpression? -> obj.toString() }
            .collect(Collectors.joining("\n\t\t"))
                + ",\n\n\tvariableDefinitions=\n\t\t" + variableDefinitions!!.stream()
            .map { obj: SExpression? -> obj.toString() }.collect(Collectors.joining("\n\t\t"))
                + "\n}")
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val that = o as SmtModel

        if (if (globalConstraints != null) globalConstraints != that.globalConstraints
            else that.globalConstraints != null
        ) {
            return false
        }
        return if (variableDefinitions != null) variableDefinitions == that.variableDefinitions else that.variableDefinitions == null
    }

    override fun hashCode(): Int {
        var result = globalConstraints?.hashCode() ?: 0
        result = 31 * result + (variableDefinitions?.hashCode() ?: 0)
        return result
    }
}
