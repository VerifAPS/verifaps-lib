package edu.kit.iti.formal.stvs.model.common;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 10.01.17.
 */
public class Selection {

    private List<Consumer<Selection>> listener;
    private IOVariable ioVariable;
    private int row;

    public Selection(IOVariable ioVariable, int row) {
        this.ioVariable = ioVariable;
        this.row = row;
    }

    public IOVariable getIoVariable() {
        return ioVariable;
    }

    public int getRow() {
        return row;
    }

    public void setIoVariable(IOVariable ioVariable) {
        this.ioVariable = ioVariable;
    }

    public void setRow(int row) {
        this.row = row;
    }

    public void addListener(Consumer<Selection> listener) {

    }
}
