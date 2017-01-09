package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import javafx.event.Event;
import javafx.event.EventTarget;
import javafx.event.EventType;

class RowEvent extends Event {
    static public EventType<RowEvent> ADD_ROW_BELOW;
    static public EventType<RowEvent> REMOVE_ROW;
    private int rowNumber;

    public RowEvent(Object source, EventTarget target, EventType<RowEvent> type, int rowNumber) {
        super(source, target, type);
    }
}
