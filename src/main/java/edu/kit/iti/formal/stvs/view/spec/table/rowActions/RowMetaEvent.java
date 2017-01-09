package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import javafx.event.Event;
import javafx.event.EventTarget;
import javafx.event.EventType;


class RowMetaEvent extends Event {
    static public EventType<RowMetaEvent> CHANGE_COMMENT;
    private int rowNumber;
    private String comment;

    public RowMetaEvent(Object source, EventTarget target, EventType<RowMetaEvent> type, int rowNumber, String comment) {
        super(source, target, type);
    }
}