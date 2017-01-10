package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class SpecificationTable<C, D> {

    private List<Consumer<ColumnChangeInfo<C>>> columnsListeners;
    private List<Consumer<RowChangeInfo<C, D>>> rowsListeners;
    private List<D> durations;

    public enum Change {
        ADD,
        REMOVE
    }

    public static class ColumnChangeInfo<C> {
        public final SpecificationColumn<C> column;
        public final VariableIdentifier columnId;
        public final Change changeType;

        public ColumnChangeInfo(SpecificationColumn<C> column, VariableIdentifier columnId, Change changeType) {
            this.column = column;
            this.columnId = columnId;
            this.changeType = changeType;
        }
    }

    public static class RowChangeInfo<C, D> {
        public final SpecificationRow<C, D> row;
        public final int rowNum;
        public final Change changeType;

        public RowChangeInfo(SpecificationRow<C, D> row, int rowNum, Change changeType) {
            this.row = row;
            this.rowNum = rowNum;
            this.changeType = changeType;
        }
    }

    public C getCell(int row, VariableIdentifier column) {
        return null;
    }

    public SpecificationColumn<C> getColumn(VariableIdentifier column) {
        return null;
    }

    public void addColumn(VariableIdentifier columnId, SpecificationColumn<C> column) {

    }

    public void removeColumn(VariableIdentifier columnId) {

    }

    public SpecificationRow<C, D> getRow(int row) {
        return null;
    }

    public void addRow(int rowNum, SpecificationRow<C, D> row) {

    }

    public void removeRow(int rowNum) {

    }

    public D getDuration(int rowNum) {
        return null;
    }

    public void addColumnsListener(Consumer<ColumnChangeInfo<C>> columnsListener) {

    }

    public void addRowsListener(Consumer<RowChangeInfo<C, D>> rowsListener) {

    }


}
