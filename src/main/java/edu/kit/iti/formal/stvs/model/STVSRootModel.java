package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import org.apache.commons.collections4.queue.CircularFifoQueue;

import java.util.List;

public class STVSRootModel {

    private List<HybridSpecification> hybridSpecifications;
    private GlobalConfig globalConfig;
    private History history;
    private CircularFifoQueue<RootModelMemento> mementos;
    private VerificationScenario scenario;

    public STVSRootModel() {
        mementos = new CircularFifoQueue<RootModelMemento>(globalConfig.getNumberOfMementos());
    }

    public List<HybridSpecification> getHybridSpecifications() {
        return hybridSpecifications;
    }

    public GlobalConfig getGlobalConfig() {
        return globalConfig;
    }

    public History getHistory() {
        return history;
    }

    public void undo() throws NoSuchMementoException {
        // applyMemento() with previous item in queue (if any)
        // Must keep track of current position in "timeline"
    }

    public void redo() throws NoSuchMementoException {
        // applyMemento() with next item in queue (if any)
        // Must keep track of current position in "timeline"
    }

    private void applyMemento(RootModelMemento memento) {

    }

    private void addOnMementoAppliedListener(Runnable listener){

    }


    public VerificationScenario getScenario() {
        return scenario;
    }
}
