package edu.kit.iti.formal.stvs.view.spec;


import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;

public class SpecificationTabController {
    public SpecificationTabController(HybridSpecification hybridSpecification, ObservableList<Type> types, ObservableList<IOVariable> ioVars) {
    }

    private ObservableSet<String> definedVars;
    private ObservableList<Type> types;
    private ObservableList<IOVariable> ioVars;
}