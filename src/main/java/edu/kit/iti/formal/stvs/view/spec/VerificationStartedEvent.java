package edu.kit.iti.formal.stvs.view.spec;


import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import javafx.event.Event;
import javafx.event.EventType;

/**
 * @author Benjamin Alt
 */
public class VerificationStartedEvent extends Event {
  private final ConstraintSpecification constraintSpec;
  public static final EventType<VerificationStartedEvent> EVENT_TYPE = new EventType
      ("Verification Started");

  public VerificationStartedEvent(ConstraintSpecification constraintSpec) {
    super(EVENT_TYPE);
    this.constraintSpec = constraintSpec;
  }

  public ConstraintSpecification getConstraintSpec() {
    return constraintSpec;
  }
}
