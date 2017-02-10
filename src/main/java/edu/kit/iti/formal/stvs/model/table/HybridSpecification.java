package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;

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

  /**
   * Constructor for an "empty" HybridSpecification that contains no cells.
   * @param editable Is this HybridSpecification supposed to be editable?
   */
  public HybridSpecification(FreeVariableList freeVariableList, boolean editable) {
    super(freeVariableList);
    this.editable = editable;
    this.selection = new Selection();
    this.counterExample = new NullableProperty<>();
    this.concreteInstance = new NullableProperty<>();
  }

  public HybridSpecification(ConstraintSpecification sourceSpec, boolean editable) {
    this(sourceSpec.getFreeVariableList(), editable);
    getColumnHeaders().addAll(sourceSpec.getColumnHeaders());
    getRows().addAll(sourceSpec.getRows());
    getDurations().addAll(sourceSpec.getDurations());
  }

  public Optional<ConcreteSpecification> getCounterExample() {
    return Optional.ofNullable(counterExample.get());
  }

  public void setCounterExample(ConcreteSpecification counterExample) {
    this.counterExample.set(counterExample);
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
    this.concreteInstance.set(concreteInstance);
  }

  public void removeConcreteInstance() {
    concreteInstance.set(null);
  }

}
