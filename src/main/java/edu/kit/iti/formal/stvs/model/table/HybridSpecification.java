package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

/**
 * @author Benjamin Alt
 */
public class HybridSpecification extends ConstraintSpecification {


  //TODO: Kann eine HybridSpecification sowohl ein Counterexample als auch eine ConcreteInstance haben?
  private Optional<ConcreteSpecification> counterExample;
  private OptionalProperty<ConcreteSpecification> concreteInstance;
  private List<Consumer<Optional<ConcreteSpecification>>> concreteInstanceChangedListeners;
  private final boolean editable;

  /**
   * Selection for Spec to Timing-Diagram synchronisation.
   * Should be created <b>once</b> on creation of this class
   */
  private Selection selection;

  public HybridSpecification(Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet, boolean editable) {
    super(typeContext, ioVariables, freeVariableSet);
    this.editable = editable;
    this.selection = new Selection();
  }

  public HybridSpecification(Map<String, SpecificationColumn<ConstraintCell>> columns, List<ConstraintDuration> durations,
                             Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet, boolean editable) {
    super(columns, durations, typeContext, ioVariables, freeVariableSet);
    this.editable = editable;
    this.selection = new Selection();
  }

  public Optional<ConcreteSpecification> getCounterExample() {
    return counterExample;
  }

  public void setCounterExample(ConcreteSpecification counterExample) {
    this.counterExample = Optional.of(counterExample);
  }

  public Selection getSelection() {
    return selection;
  }

  /**
   * TODO: Should we keep this? It's really just convenience for getCounterExample().get().getColumn(column).getCells()
   */
  @Deprecated
  public List<ConcreteCell> getConcreteValuesForConstraint(String column, int row) {
    throw new UnsupportedOperationException("This method is on the kill list and may be removed at any time. For alternatives," +
        "" +
        "check the Javadoc of this method");
    /* Check counterexample first
    if (counterExample.isPresent()) {
      return counterExample.get().getColumn(column).getCells();
    } else if (concreteInstance.get() != null) {
      return concreteInstance.get().getColumn(column).getCells();
    } else {
      //TODO: Should I throw an exception here?
      return null;
    }*/
  }

  /**
   * TODO: Should we keep this? It's really just convenience for getCounterExample().get().getDuration(row)
   */
  @Deprecated
  public ConcreteDuration getConcreteDurationForRow(int row) {
    throw new UnsupportedOperationException("This method is on the kill list and may be removed at any time. For alternatives," +
        "" +
        "check the Javadoc of this method");
    /*
    if (counterExample.isPresent()) {
      return counterExample.get().getDuration(row);
    } else if (concreteInstance.get() != null) {
      return concreteInstance.get().getDuration(row);
    }*/
  }

  public boolean isEditable() {
    return editable;
  }

  public ConcreteSpecification getConcreteInstance() {
    return concreteInstance.get();
  }

  public OptionalProperty<ConcreteSpecification> concreteInstanceProperty() {
    return concreteInstance;
  }

  public void setConcreteInstance(ConcreteSpecification concreteInstance) {
    this.concreteInstance.set(concreteInstance);
  }

  public void removeConcreteInstance() {
    concreteInstance.clear();
  }
}
