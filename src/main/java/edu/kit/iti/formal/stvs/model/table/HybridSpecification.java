package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;
import edu.kit.iti.formal.stvs.logic.specification.BacktrackSpecificationConcretizer;
import edu.kit.iti.formal.stvs.logic.specification.ConcretizerContext;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.*;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableSet;

/**
 * A ConstraintSpecification which also has an associated counterexample (ConcreteSpecification),
 * concrete instance (ConcreteSpecification) or both.
 * This class is the model on which the
 * {@link TablePaneController}
 * and {@link TimingDiagramCollectionController}
 * operate. This class is responsible for triggering the generation of a new concrete instance of a
 * specification whenever one of its {@link ConstraintCell}s or {@link ConstraintDuration}s change
 * or new cells or durations are added.
 * @author Benjamin Alt
 */
public class HybridSpecification extends ConstraintSpecification {

  private ConcreteSpecification counterExample;
  private OptionalProperty<ConcreteSpecification> concreteInstance;
  private final boolean editable;
  private SpecificationConcretizer concretizer;

  /**
   * Selection for Spec to Timing-Diagram synchronisation.
   * Should be created <b>once</b> on creation of this class
   */
  private Selection selection;

  /**
   * Constructor for an "empty" HybridSpecification that contains no cells.
   * @param ioVariables The IO variables declared in the code
   * @param freeVariableSet The set of declared free variables
   * @param editable Is this HybridSpecification supposed to be editable?
   */
  public HybridSpecification(ObjectProperty<List<Type>> typeContext,
                             ObjectProperty<List<CodeIoVariable>> ioVariables,
                             FreeVariableSet freeVariableSet,
                             boolean editable) {
    super(typeContext, ioVariables, freeVariableSet);
    this.editable = editable;
    this.selection = new Selection();
    concreteInstance = new OptionalProperty<>(new SimpleObjectProperty<>());
    validSpecificationProperty().addListener((observable, oldValue, newValue) -> onValidSpecificationChanged());
    concretizer = new BacktrackSpecificationConcretizer(new ConcretizerContext());
    concretizer.concreteSpecProperty().addListener((observable, oldValue, newValue) -> onConcreteSpecificationChanged());
  }

  public HybridSpecification(ConstraintSpecification sourceSpec, boolean editable) {
    this(sourceSpec.typeContextProperty(),
        sourceSpec.codeIoVariablesProperty(),
        sourceSpec.getFreeVariableSet(),
        editable);
    getSpecIoVariables().addAll(sourceSpec.getSpecIoVariables());
    getRows().addAll(sourceSpec.getRows());
    getDurations().addAll(sourceSpec.getDurations());
  }

  public ConcreteSpecification getCounterExample() {
    return counterExample;
  }

  public void setCounterExample(ConcreteSpecification counterExample) {
    this.counterExample = counterExample;
  }

  public Selection getSelection() {
    return selection;
  }

  public Boolean isEditable() {
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

  /**
   * Called every time a new valid specification is available.
   * Triggers a concretization.
   */
  private void onValidSpecificationChanged() {
    concretizer.createConcreteSpecification(getValidSpecification());
  }

  private void onConcreteSpecificationChanged() {
    ConcreteSpecification newConcreteSpec = concretizer.getConcreteSpec();
    if(newConcreteSpec != null) {
      concreteInstance.set(newConcreteSpec);
    } else {
      concreteInstance.clear();
    }
  }

}
