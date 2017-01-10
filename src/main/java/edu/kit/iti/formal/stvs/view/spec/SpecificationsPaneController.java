package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import javafx.collections.ObservableList;

public class SpecificationsPaneController {
    public SpecificationsPaneController(ObservableList<Type> types, ObservableList<IOVariable> ioVars, ObservableList<HybridSpecification> hybridSpecifications) {
    }

    private ObservableList<HybridSpecification> hybridSpecifications;

    public ObservableList<HybridSpecification> getHybridSpecifications() {
        return null;
    }

    private ObservableList<Type> types;
    private ObservableList<IOVariable> ioVars;
}
