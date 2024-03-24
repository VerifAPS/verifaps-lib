package edu.kit.iti.formal.stvs.model.common

import javafx.beans.Observable
import javafx.beans.property.*
import javafx.util.Callback

/**
 * A free variable. Free variables have a name, a type and a default value and can occur in
 * constraint expressions.
 * @author Philipp
 */
class FreeVariable @JvmOverloads
/**
 * Creates a free variable with a name and type. A default value will be generated through
 * [Type.generateDefaultValue].
 *
 * @param name Name of the free variable
 * @param type Identifier of the type of the free variable
 */
constructor(name: String?, type: String?, constraint: String? = null) : Variable {
    val nameProperty: StringProperty = SimpleStringProperty(name)
    val typeProperty: StringProperty = SimpleStringProperty(type)
    val constraintProperty: StringProperty = SimpleStringProperty(constraint ?: DONTCARE)

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

    var constraint: String?
        get() = constraintProperty.get()
        set(value) = constraintProperty.set(value)

    override fun toString(): String = "FreeVariable{name=$name, type=$type, constraint=$constraint}"
    override var type: String
        get() = typeProperty.get()
        set(value) = typeProperty.set(value)

    override var name: String?
        get() = nameProperty.get()
        set(value) = nameProperty.set(value)

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
