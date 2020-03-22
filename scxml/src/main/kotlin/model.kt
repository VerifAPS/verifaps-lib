import org.jdom2.Document
import org.jdom2.Element
import kotlin.properties.ReadOnlyProperty
import kotlin.reflect.KClass
import kotlin.reflect.KProperty

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/22/20)
 */

inline class IdRef(val value: String)

data class SCXml(val element: Element) {
    constructor(element: Document) : this(element.rootElement)

    /** A legal state specification. See 3.11 Legal State Configurations and Specifications for details.
     * The id of the initial state(s) for the document. If not specified, the default initial state is
     * the first child state in document order.*/
    val initial: IdRef? by element.attribute().asIdRef()

    /**
     * The name of this state machine. It is for purely informational purposes.
     */
    val name: String? by element.attribute()
    //xmlns    true    none    URI    none    The value must be "http://www.w3.org/2005/07/scxml".
    /**    The value must be "1.0"
     */
    val version: String by element.attribute("1.0")

    /**  The datamodel that this document requires. "null" denotes the Null datamodel, "ecmascript"
     * the ECMAScript datamodel, and "xpath" the XPath datamodel, as defined in B Data Models.*/
    val datamodel: String? by element.attribute()

    /** The data binding to use. See 5.3.3 Data Binding for details.*/
    val binding: String? by element.attribute()

    /** A compound or atomic state. Occurs zero or more times. See 3.3 <state> for details. */
    val states by element.children("state", State::class)

    /* A parallel state. Occurs zero or more times. See 3.4 <parallel> for details.*/
    val parallels by element.children("parallel", ParallelState::class)

    /**A top-level final state in the state machine. Occurs zero or more times. The SCXML processor must terminate processing when the state machine reaches this state. See 3.7 <final> for details*/
    val finals by element.children("final", FinalState::class)

    //<datamodel> Defines part or all of the data model. Occurs 0 or 1 times. See 5.2 <datamodel>
    //<script> Provides scripting capability. Occurs 0 or 1 times. 5.8 <script>
}

open class AbstractState(val element: Element) {
    /**    Defines an outgoing transition from this state. Occurs 0 or more times. See 3.5 <transition>
     */
    val transitions by element.children("transition", Transition::class)

    /** Defines a sequential substate of the parent state. Occurs 0 or more times.*/
    val states by element.children("state", State::class)

    /** Defines a parallel substate. Occurs 0 or more times. See 3.4 <parallel>*/
    val parallels by element.children("parallels", ParallelState::class)

    /** A child pseudo-state which records the descendant state(s) that the parent state was in the last time the system transitioned from the parent. May occur 0 or more times. See 3.10 <history>.
     */
    val history by element.children("history", HistoryState::class)

}

class State(element: Element) : AbstractState(element) {
    val id: String? by element.attribute()
    val _attributeInitial: String? by element.attribute()

    /**Definition: An atomic state is a <state> that has no <state>, <parallel> or <final> children.*/
    val atomic: Boolean
        get() = false

    /** Definition: A compound state is a <state> that has <state>, <parallel>, or <final> children
     * (or a combination of these).
     */
    val compound: Boolean
        get() = false

    //<onentry> Optional element holding executable content to be run upon entering this <state>. Occurs 0 or more times. See 3.8 <onentry>
    //<onexit> Optional element holding executable content to be run when exiting this <state>. Occurs 0 or more times. See 3.9 <onexit>
    //<datamodel> Defines part or all of the data model. Occurs 0 or 1 times. See 5.2 <datamodel>
    //<invoke> Invokes an external service. Occurs 0 or more times. See 6.4 <invoke> for details.


    /** In states that have substates, an optional child which identifies the default initial state.
     * Any transition which takes the parent state as its target will result in the state machine
     * also taking the transition contained inside the <initial> element. See 3.6 <initial>
     */
    val initial by element.children("initial", String::class)

    /**Defines a final substate. Occurs 0 or more times. See 3.7 <final >.*/
    val final by element.children("final", FinalState::class)

}

class Transition(val element: Element) {
    /**A space-separated list of event descriptors. See 3.12.1 Event Descriptors for details.
     * A list of designators of events that trigger this transition. See 3.13 Selecting and
     * Executing Transitions for details on how transitions are selected and executed.
     * See E Schema for the definition of the datatype.**/
    val event: String? by element.attribute()

    /** Any boolean expression. See 5.9.1 Conditional Expressions for details.
    The guard condition for this transition. See 3.13 Selecting and Executing Transitions for details.*/
    val cond: String? by element.attribute("false")

    /**
    A legal state specification.See 3.11 Legal State Configurations and Specifications for details.
    The identifier(s) of the state or parallel region to transition to. See 3.13 Selecting and Executing
    Transitions for details.
     */
    val target: IdRef? by element.attribute().asIdRef()

    /**    "internal" "external"
     * Determines whether the source state is exited in transitions whose target state is a descendant of the source state.
     * See 3.13 Selecting and Executing Transitions for details.
     */
    val type: String? by element.attribute()
}

class ParallelState(element: Element) : AbstractState(element) {
    val id: String? by element.attribute()
}

class FinalState(element: Element) {
    val id: String? by element.attribute()
}

class InitialState(val element: Element) {
    /**    Defines an outgoing transition from this state. Occurs 0 or more times. See 3.5 <transition>
     */
    val transitions by element.children("transition", Transition::class)
}

class HistoryState(val element: Element) {
    /**     A valid id as defined in [XML Schema]	Identifier for this pseudo-state. See 3.14 IDs for details.*/
    val id: String? by element.attribute()

    /** Default:	"shallow", 	"deep" or "shallow",
    Determines whether the active atomic substate(s) of the current state or only its immediate active
    substate(s) are recorded.
     */
    val type: String by element.attribute("shallow")

    val isDeep
        get() = type == "deep"

    val isShallow
        get() = type == "shallow"

}


private fun <T : Any> Element.children(tagName: String, kClass: KClass<T>) =
        object {
            operator fun getValue(instance: Any, prop: KProperty<*>): List<T> {
                return this@children.getChildren(tagName).map {
                    kClass.constructors.first().call(it)
                }
            }
        }

private fun <T : Any> Element.child(tagName: String, kClass: KClass<T>) =
        object {
            operator fun getValue(instance: Any, prop: KProperty<*>): T? {
                return this@child.getChild(tagName)?.let {
                    kClass.constructors.first().call(it)
                }
            }
        }

private fun Element.attribute(defaultValue: String) = object {
    operator fun getValue(instance: Any, prop: KProperty<*>): String {
        return this@attribute.getAttributeValue(prop.name) ?: defaultValue
    }
}

private fun Element.attribute(): ReadOnlyProperty<Any, String?> = object : ReadOnlyProperty<Any, String?> {
    override operator fun getValue(thisRef: Any, property: KProperty<*>): String? {
        return this@attribute.getAttributeValue(property.name)
    }
}

private fun ReadOnlyProperty<Any, String?>.asIdRef(): ReadOnlyProperty<Any, IdRef?> =
        object : ReadOnlyProperty<Any, IdRef?> {
            override fun getValue(thisRef: Any, property: KProperty<*>): IdRef? {
                return this@asIdRef.getValue(thisRef, property)?.let { IdRef(it) }
            }
        }