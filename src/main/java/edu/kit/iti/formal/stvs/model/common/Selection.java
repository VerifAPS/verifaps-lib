package edu.kit.iti.formal.stvs.model.common;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created by csicar on 10.01.17.
 */
public class Selection {

    private List<Consumer<Selection>> listener;
    private Optional<String> column;
    private Optional<Integer> row;

    public Selection(String column, int row) {
        this.column = Optional.ofNullable(column);
        this.row = Optional.ofNullable(row);
    }

    public Selection() {
        this.column = Optional.empty();
        this.row = Optional.empty();
    }

    public Optional<String> getColumn() {
        return column;
    }

    public Optional<Integer> getRow() {
        return row;
    }

    public void setColumn(String column) {
        this.column = Optional.ofNullable(column);
    }

    public void setRow(int row) {
        this.row = Optional.ofNullable(row);
    }

    public void addListener(Consumer<Selection> listener) {

    }
}
