package edu.kit.iti.formal.stvs.view.spec;


import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import javafx.event.Event;
import javafx.event.EventType;

/**
 * @author Benjamin Alt
 */
public class VerificationEvent extends Event {
  private final ConstraintSpecification constraintSpec;
  private final Type type;

  public static final EventType<VerificationEvent> EVENT_TYPE = new EventType("Verification Event");

  public VerificationEvent(ConstraintSpecification constraintSpec, Type type) {
    super(EVENT_TYPE);
    this.constraintSpec = constraintSpec;
    this.type = type;
  }

  public ConstraintSpecification getConstraintSpec() {
    return constraintSpec;
  }

  public Type getType() {
    return type;
  }

  public enum Type {
    START, STOP
  }
}
