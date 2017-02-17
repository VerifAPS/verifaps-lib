package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.view.spec.variables.clipboard.Json;
import javafx.collections.ObservableList;

import java.util.Optional;

/**
 * A ConstraintSpecification which also has an associated counterexample (ConcreteSpecification),
 * concrete instance (ConcreteSpecification) or both.
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
   * Selection for Spec to Timing-Diagram synchronisation.
   * Should be created <b>once</b> on creation of this class
   */
  private Selection selection;

  public HybridSpecification(FreeVariableList freeVariableList, boolean editable) {
    this(DEFAULT_NAME, freeVariableList, editable);
  }

  /**
   * Constructor for an "empty" HybridSpecification that contains no cells.
   * @param editable Is this HybridSpecification supposed to be editable?
   */
  public HybridSpecification(String name, FreeVariableList freeVariableList, boolean editable) {
    super(name, freeVariableList);
    this.editable = editable;
    this.selection = new Selection();
    this.counterExample = new NullableProperty<>();
    this.concreteInstance = new NullableProperty<>();
  }

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
      // Concrete specification columns may be "shorter" (have less rows) than hybrid spec (i.e. for
      // some counterexamples), so cannot check rows
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
