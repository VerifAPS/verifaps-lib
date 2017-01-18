package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Created by philipp on 10.01.17.
 */
public class HybridSpecification extends ConstraintSpecification {


  private Optional<ConcreteSpecification> counterExample;
  private Optional<ConcreteSpecification> concreteInstance;
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
  }

  /**
   * Copy constructor
   *
   * @param spec The spec to copy
   */
  public HybridSpecification(HybridSpecification spec) {
    super(null);
    //...
    this.editable = spec.editable;
  }

  public Optional<ConcreteSpecification> getCounterExample() {
    return counterExample;
  }

  public void setCounterExample(ConcreteSpecification counterExample) {
  }

  public void removeConcreteInstance() {

  }

  public void addConcreteInstanceChangedListener(Consumer<Optional<ConcreteSpecification>> listener) {

  }

  public Selection getSelection() {
    return selection;
  }


  public List<ConcreteCell> getConcreteValuesForConstraint(String column, int row) {
    return null;
  }

  public ConcreteDuration getDurationForRow(int row) {
    return null;
  }

  public boolean isEditable() {
    return editable;
  }
}
