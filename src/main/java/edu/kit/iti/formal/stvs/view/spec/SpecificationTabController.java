package edu.kit.iti.formal.stvs.view.spec;


import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;

public class SpecificationTabController implements Controller {
    public SpecificationTabController(HybridSpecification hybridSpecification, ObservableList<Type> types, ObservableList<IOVariable> ioVars) {
    }

    private ObservableSet<String> definedVars;
    private ObservableList<Type> types;
    private ObservableList<IOVariable> ioVars;

    public SpecificationTab getView() {
        return null;
    }
}