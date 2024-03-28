package edu.kit.iti.formal.stvs.model.common

import edu.kit.iti.formal.stvs.model.config.ColumnConfig
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.table.Commentable
import edu.kit.iti.formal.stvs.model.table.ValidSpecification
import javafx.beans.property.ObjectProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import tornadofx.getValue
import tornadofx.setValue

/**
 * Base class for input/output variables.
 *
 * @author Benjamin Alt
 */
sealed class IoVariable : Variable {
    abstract override val name: String
    abstract override val type: String
    abstract val category: VariableCategory

    /**
     * Is this IoVariable equivalent to another variable, in the sense that its name, type and
     * category are identical to those of the other IoVariable? This is not the same as equals(),
     * because it may be desirable that instances of different child classes (e.g. SpecIoVariable
     * and CodeIoVariable) match, but are not equals because they are instances of different classes.
     * @param other The IoVariable to compare this instance to
     * @return True if the IoVariables match, false otherwise
     */
    fun matches(other: IoVariable): Boolean {
        return name == other.name && type == other.type && this.category == other.category
    }

    val varDescriptor: String
        get() = this.category.toString() + " " + name + " : " + type
}

/**
 * An input or output variable declared in the code.
 *
 * @author Philipp
 */
data class CodeIoVariable(
    override val category: VariableCategory,
    override val type: String,
    override val name: String
) : IoVariable() {
    override fun toString(): String {
        return "CodeIoVariable($category $name : $type)"
    }
}

/**
 * A valid I/O variable. This variable may appear in a [ValidSpecification]. Their names
 * have been checked (conform to valid identifier pattern) and their types are parsed
 * [Type] objects. For the validation logic, see
 * [edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator].
 *
 * @author Philipp
 */
data class ValidIoVariable(
    override val category: VariableCategory,
    override val name: String,
    val validType: Type
) :
    IoVariable() {
    override val type: String
        get() = validType.typeName
}


/**
 * An input/output variable in a specification table.
 * @author Philipp
 */
class SpecIoVariable() : IoVariable(), Commentable {
    val nameProperty: StringProperty = SimpleStringProperty()
    override var name: String by nameProperty

    val typeProperty: StringProperty = SimpleStringProperty()
    override var type: String by typeProperty


    val categoryProperty: ObjectProperty<VariableCategory> = SimpleObjectProperty()
    override var category by categoryProperty


    val roleProperty: ObjectProperty<VariableRole> = SimpleObjectProperty()
    var role by roleProperty

    var columnConfig = ColumnConfig()

    override val commentProperty: StringProperty = SimpleStringProperty("")

    /**
     * Creates a variable that appears in the specification.
     * role will be the standard role for the given category
     * @param category The category of the variable
     * @param typeIdentifier The identifier of the type of the variable
     * @param name The name of the Variable
     */
    constructor(
        category: VariableCategory,
        role: VariableRole = category.defaultRole,
        typeIdentifier: String,
        name: String
    ) : this() {
        this.category = category
        this.role = role
        this.type = typeIdentifier
        this.name = name
    }

    /**
     * Copy constructor: Create a deep copy of a given SpecIoVariable.
     * @param specIoVariable The SpecIoVariable to copy
     */
    constructor(specIoVariable: SpecIoVariable)
            : this(specIoVariable.category, specIoVariable.role, specIoVariable.type, specIoVariable.name)

    override fun toString(): String {
        return "SpecIoVariable($category $name : $type)"
    }
}

