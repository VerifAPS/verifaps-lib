package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import javafx.event.Event;
import javafx.event.EventTarget;
import javafx.event.EventType;

/**
 * This event is fired if a view component triggers a change that is applicable to one specific row
 */
public class RowEvent extends Event {
    static public EventType<RowEvent> ADD_ROW_BELOW;
    static public EventType<RowEvent> REMOVE_ROW;
    static public EventType<RowEvent> COMMENT_ROW;
    private int rowNumber;

    public RowEvent(Object source, EventTarget target, EventType<RowEvent> type, int rowNumber) {
        super(source, target, type);
    }
}
