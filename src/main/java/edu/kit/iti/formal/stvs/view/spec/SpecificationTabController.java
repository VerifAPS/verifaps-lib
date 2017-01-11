package edu.kit.iti.formal.stvs.view.spec;


import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.logic.specification.VerificationState;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.collections.ObservableSet;

public class SpecificationTabController implements Controller {
    public SpecificationTabController(HybridSpecification hybridSpecification, ObservableList<Type> types, ObservableList<IOVariable> ioVars, VerificationState state) {
    }

    private ObservableSet<String> definedVars;
    private ObservableList<Type> types;
    private ObservableList<IOVariable> ioVars;
    private HybridSpecification spec;
    private VerificationState state;

    public SpecificationTab getView() {
        return null;
    }

    private void onVerificationStart(){
        //fireEvent("")
    }
}