package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

import javafx.event.Event;
import javafx.event.EventType;

/**
 * Event that is fired when the verification button is pressed The event is delegated along the
 * scenegraph and is caught in {@link edu.kit.iti.formal.stvs.view.StvsRootController} to start/stop
 * the verification
 *
 * @author Benjamin Alt
 */
public class VerificationEvent extends Event {
  public static final EventType<VerificationEvent> EVENT_TYPE = new EventType("Verification Event");
  private final ConstraintSpecification constraintSpec;
  private final Type type;

  /**
   * creates an event.
   *
   * @param constraintSpec The spec that
   * @param type type of the event
   */
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
