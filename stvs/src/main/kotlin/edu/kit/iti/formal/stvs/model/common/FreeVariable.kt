package edu.kit.iti.formal.stvs.model.common

import javafx.beans.Observable
import javafx.beans.property.*
import javafx.util.Callback
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import tornadofx.getValue
import tornadofx.setValue

/**
 * A free variable. Free variables have a name, a type and a default value and can occur in
 * constraint expressions.
 * @author Philipp
 */
@Serializable
class FreeVariable : Variable {
    @Transient
    val nameProperty: StringProperty = SimpleStringProperty()
    override var name by nameProperty

    @Transient
    val typeProperty: StringProperty = SimpleStringProperty()
    override var type by typeProperty

    @Transient
    val constraintProperty: StringProperty = SimpleStringProperty(DONTCARE)
    var constraint by constraintProperty

    /**
     * Creates a free variable with a name and type. A default value will be generated through
     * [Type.generateDefaultValue].
     *
     * @param name Name of the free variable
     * @param type Identifier of the type of the free variable
     */
    constructor(name: String?, type: String?, constraint: String? = null) {
        this.name = name
        this.type = type
        this.constraint = constraint ?: DONTCARE
    }

    /**
     * Creates a free variable with a name, type and default value.
     *
     * @param name Name of the free variable
     * @param type Identifier of the type of the free variable
     * @param constraint Default value of the free variable
     */

    /**
     * Copy constructor: Makes a deep copy of a given free variable.
     * @param freeVar The variable to copy
     */
    constructor(freeVar: FreeVariable) : this(freeVar.name, freeVar.type, freeVar.constraint)

    override fun toString(): String = "FreeVariable{name=$name, type=$type, constraint=$constraint}"

    companion object {
        /**
         * The default extractor to allow observable collections containing FreeVariables to fire
         * change events when the properties of a FreeVariable change.
         */
        val EXTRACTOR: Callback<FreeVariable?, Array<Observable>> = Callback { freeVar: FreeVariable? ->
            arrayOf(freeVar!!.nameProperty, freeVar.typeProperty, freeVar.constraintProperty)
        }
        private const val DONTCARE = "-"
    }
}
