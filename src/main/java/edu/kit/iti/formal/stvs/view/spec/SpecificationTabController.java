package edu.kit.iti.formal.stvs.view.spec;


import javafx.collections.ObservableSet;

class SpecificationTabController {
    public SpecificationTabController(HybridTables hybridTable, ObservableList<Type> types, ObservableList<IOVariables> ioVars) {
    }

    private ObservableSet<String> definedVars;
    private ObservableList<Type> types;
    private ObservableList<IOVariables> ioVars;
}