package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.logic.verification.VerificationState;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.TabPane;

public class SpecificationsPaneController implements Controller {
    public SpecificationsPaneController(ObservableList<HybridSpecification> hybridSpecifications, ObjectProperty<VerificationState> state, GlobalConfig globalConfig) {
    }

    private GlobalConfig globalConfig;
    private ObservableList<HybridSpecification> hybridSpecifications;

    public ObservableList<HybridSpecification> getHybridSpecifications() {
        return null;
    }

    private TabPane view;
    private ContextMenu contextMenu;


    public TabPane getView() {
        return view;
    }

    private void addTab(HybridSpecification spec) {

    }

    private void removeTab(int tabIndex) {

    }
}
