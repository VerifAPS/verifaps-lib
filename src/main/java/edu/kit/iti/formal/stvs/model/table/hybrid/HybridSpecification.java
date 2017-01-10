package edu.kit.iti.formal.stvs.model.table.hybrid;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintSpecification;

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

    /**
     * Selection for Spec to Timing-Diagram synchronisation.
     * Should be created <b>once</b> on creation of this class
     */
    private Selection selection;

    public HybridSpecification(Set<Type> typeContext, Set<IOVariable> ioVariables) {
        super(typeContext, ioVariables);
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
        return null;
    }

    public List<ConcreteCell> getConcreteValuesForConstraint(VariableIdentifier column, int row) {
        return null;
    }

    public ConcreteDuration getDurationForRow(int row) {
        return null;
    }

}
