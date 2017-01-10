package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.view.spec.table.TablePane;
import edu.kit.iti.formal.stvs.view.timingdiagram.TimingDiagramCollectionView;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

public class SpecificationTab extends VBox{
    private TablePane table;
    private TimingDiagramCollectionView diagram;
    public SpecificationTab() {
    }

    public TablePane getTable() {
        return table;
    }

    public void setTable(TablePane table) {
        this.table = table;
    }

    public TimingDiagramCollectionView getDiagram() {
        return diagram;
    }

    public void setDiagram(TimingDiagramCollectionView diagram) {
        this.diagram = diagram;
    }
}
