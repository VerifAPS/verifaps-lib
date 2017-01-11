package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.io.VerificationScenario;
import edu.kit.iti.formal.stvs.model.memento.NoSuchMementoException;
import edu.kit.iti.formal.stvs.model.memento.RootModelMemento;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import org.apache.commons.collections4.queue.CircularFifoQueue;

import java.util.HashSet;

public class STVSRootModel {
    private final int NUMBER_OF_MEMENTOS = 100;

    private HashSet<HybridSpecification> hybridSpecifications;
    private GlobalConfig globalConfig;
    private History history;
    private CircularFifoQueue<RootModelMemento> mementos;
    private Code code;
    private VerificationScenario scenario;

    public STVSRootModel() {
        mementos = new CircularFifoQueue<RootModelMemento>(NUMBER_OF_MEMENTOS);
    }

    public HashSet<HybridSpecification> getHybridSpecifications() {
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

    public Code getCode() {
        return code;
    }

    public void setCode(Code code) {
        this.code = code;
    }

    public VerificationScenario getScenario() {
        return scenario;
    }
}
