package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Created by philipp on 10.01.17.
 */
public class HybridSpecification extends ConstraintSpecification {

    private Optional<ConcreteSpecification> concreteInstance;
    private List<Consumer<Optional<ConcreteSpecification>>> concreteInstanceChangedListeners;
    private final boolean editable;

    /**
     * Selection for Spec to Timing-Diagram synchronisation.
     * Should be created <b>once</b> on creation of this class
     */
    private Selection selection;

    public HybridSpecification(Set<Type> typeContext, Set<IOVariable> ioVariables, FreeVariableSet freeVariableSet, boolean editable) {
        super(typeContext, ioVariables, freeVariableSet);
        this.editable = editable;
    }

    /**
     * Copy constructor
     * @param spec The spec to copy
     */
    public HybridSpecification(HybridSpecification spec) {
        //...
        this.editable = spec.editable;
    }

    public Optional<ConcreteSpecification> getConcreteInstance() {
        return concreteInstance;
    }

    public void setConcreteInstance(ConcreteSpecification concreteInstance) {
    }

    public void removeConcreteInstance() {

    }

    public void addConcreteInstanceChangedListener(Consumer<Optional<ConcreteSpecification>> listener) {

    }

    public Selection getSelection() {
        return selection;
    }

    public List<ConcreteCell> getConcreteValuesForConstraint(VariableIdentifier column, int row) {
        return null;
    }

    public ConcreteDuration getDurationForRow(int row) {
        return null;
    }

    public boolean isEditable() {
        return editable;
    }
}
