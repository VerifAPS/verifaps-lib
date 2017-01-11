package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.logic.specification.VerificationState;
import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.TabPane;

public class SpecificationsPaneController implements Controller {
    public SpecificationsPaneController(ObservableList<Type> types, ObservableList<CodeIOVariable> ioVars, ObservableList<HybridSpecification> hybridSpecifications, ObjectProperty<VerificationState> state, GlobalConfig globalConfig) {
    }

    private GlobalConfig globalConfig;
    private ObservableList<HybridSpecification> hybridSpecifications;

    public ObservableList<HybridSpecification> getHybridSpecifications() {
        return null;
    }

    private ObservableList<Type> types;
    private ObservableList<CodeIOVariable> ioVars;
    private TabPane view;


    public TabPane getView() {
        return view;
    }

    private void addTab(HybridSpecification spec) {

    }

    private void removeTab(int tabIndex) {

    }
}
