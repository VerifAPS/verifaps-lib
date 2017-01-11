package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.beans.property.IntegerProperty;
import javafx.collections.ObservableList;
import javafx.scene.Node;

import java.util.List;

/**
 * Created by leonk on 10.01.2017.
 */
public abstract class ColumnController implements Controller {
    public ColumnController(ColumnConfig config) {

    }

    public abstract void onProblemsChange(List<SpecProblem> problems);

    public abstract IntegerProperty getWidthProperty();

    public abstract int getWidth();

    public abstract ObservableList<HybridCellController> getCells();

    @Override
    public abstract Node getView();
}
