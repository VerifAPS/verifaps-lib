package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.clipboard.Json;
import javafx.collections.ObservableList;

import java.util.Optional;

/**
 * A {@link ConstraintSpecification} which also has an associated counterexample
 * (a {@link ConcreteSpecification}), a concrete instance ({@link ConcreteSpecification}) or both.
 * This class is the model on which the
 * {@link edu.kit.iti.formal.stvs.view.spec.SpecificationController}
 * and {@link TimingDiagramCollectionController} operate.
 * @author Benjamin Alt
 */
public class HybridSpecification extends ConstraintSpecification {

  private final NullableProperty<ConcreteSpecification> counterExample;
  private final NullableProperty<ConcreteSpecification> concreteInstance;
  private final boolean editable;

  /**
   * Stores which cell in the table is currently highlighted in the view. This is saved here in
   * order to allow the table and timing diagram to share the same reference.
   */
  private Selection selection;

  /**
   * Create a new, empty hybrid specification with a default name from a list of free variables.
   * @param freeVariableList A list of initial free variables
   * @param editable True if this hybridSpecification is editable, false otherwise
   */
  public HybridSpecification(FreeVariableList freeVariableList, boolean editable) {
    this(DEFAULT_NAME, freeVariableList, editable);
  }

  /**
   * Create a new, empty hybrid specification with a given name and a list of free variables.
   * @param name The name of the HybridSpecification
   * @param freeVariableList A list of initial free variables
   * @param editable True if this HybridSpecification is editable, false otherwise
   */
  public HybridSpecification(String name, FreeVariableList freeVariableList, boolean editable) {
    super(name, freeVariableList);
    this.editable = editable;
    this.selection = new Selection();
    this.counterExample = new NullableProperty<>();
    this.concreteInstance = new NullableProperty<>();
  }

  /**
   * Create a HybridSpecification from a {@link ConstraintSpecification}.
   * @param sourceSpec The original {@link ConstraintSpecification}
   * @param editable True if this HybridSpecification is editable, false otherwise
   */
  public HybridSpecification(ConstraintSpecification sourceSpec, boolean editable) {
    this(sourceSpec.getName(), sourceSpec.getFreeVariableList(), editable);
    getColumnHeaders().addAll(sourceSpec.getColumnHeaders());
    getRows().addAll(sourceSpec.getRows());
    getDurations().addAll(sourceSpec.getDurations());
  }

  public Optional<ConcreteSpecification> getCounterExample() {
    return Optional.ofNullable(counterExample.get());
  }

  public void setCounterExample(ConcreteSpecification counterExample) {
    if (counterExample != null) {
      if (!columnHeadersMatch(counterExample.columnHeaders)) {
        throw new IllegalArgumentException("The column headers of the concrete instance are not " +
            "compatible with this hybrid specification");
      }
      this.counterExample.set(counterExample);
    }
  }

  public Selection getSelection() {
    return selection;
  }

  public boolean isEditable() {
    return editable;
  }

  public Optional<ConcreteSpecification> getConcreteInstance() {
    return Optional.ofNullable(concreteInstance.get());
  }

  public NullableProperty<ConcreteSpecification> concreteInstanceProperty() {
    return concreteInstance;
  }

  public NullableProperty<ConcreteSpecification> counterExampleProperty() {
    return counterExample;
  }

  public void setConcreteInstance(ConcreteSpecification concreteInstance) {
    if (concreteInstance != null) {
      if (!columnHeadersMatch(concreteInstance.columnHeaders)) {
        throw new IllegalArgumentException("The column headers of the concrete instance are not " +
            "compatible with this hybrid specification");
      }
      this.concreteInstance.set(concreteInstance);
    }
  }

  private boolean columnHeadersMatch(ObservableList<ValidIoVariable> columnHeaders) {
    if (this.columnHeaders.size() != columnHeaders.size()) {
      return false;
    }
    for (int i = 0; i < this.columnHeaders.size(); i++) {
      if (!this.columnHeaders.get(i).matches(columnHeaders.get(i))) return false;
    }
    return true;
  }

  public void removeConcreteInstance() {
    concreteInstance.set(null);
  }

}
