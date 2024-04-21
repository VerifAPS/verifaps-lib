package edu.kit.iti.formal.stvs.view.spec

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import javafx.event.Event
import javafx.event.EventType

/**
 * Event that is fired when the verification button is pressed The event is delegated along the
 * scene graph and is caught in [edu.kit.iti.formal.stvs.view.StvsRootController] to
 * start/stop the verification.
 *
 * @author Benjamin Alt
 */
data class VerificationEvent(val constraintSpec: ConstraintSpecification, val type: Type) : Event(EVENT_TYPE) {
    enum class Type {
        START, STOP
    }

    companion object {
        val EVENT_TYPE = EventType<VerificationEvent>("Verification Event")
    }
}
