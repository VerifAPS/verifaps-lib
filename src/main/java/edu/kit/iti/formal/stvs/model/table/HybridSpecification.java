package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.logic.specification.BacktrackSpecificationConcretizer;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.value.ObservableValue;

import javafx.beans.value.ChangeListener;

import java.util.ArrayList;
import java.util.List;
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
  private SpecificationConcretizer concretizer;

  /**
   * Selection for Spec to Timing-Diagram synchronisation.
   * Should be created <b>once</b> on creation of this class
   */
  private Selection selection;

  public HybridSpecification(Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet, boolean editable) {
    super(typeContext, ioVariables, freeVariableSet);
    this.editable = editable;
    this.selection = new Selection();
    validSpecificationProperty().addListener(new ValidSpecificationChangedListener<ValidSpecification>());
    concretizer = new BacktrackSpecificationConcretizer();
    concretizer.concreteSpecProperty().addListener(new ConcreteSpecificationChangedListener<ConcreteSpecification>());
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
   * A row in a ConcreteSpecification is not the same as a row in a ConstraintSpecification. This function does the
   * mapping between the two.
   */
  public List<ConcreteCell> getConcreteValuesForConstraint(String column, int row) {
    if (counterExample.isPresent()) {
      int startIndex = counterExample.get().getDuration(row).getBeginCycle();
      int endIndex = counterExample.get().getDuration(row).getEndCycle();
      ArrayList<ConcreteCell> concreteCells = new ArrayList<>();
      for (int i = startIndex; i < endIndex + 1; i++) {
        concreteCells.add(counterExample.get().getCell(i, column));
      }
      return concreteCells;
    } else {
      return new ArrayList<ConcreteCell>();
    }

  }

  /**
   * This is necessary as "row" means something else in the counterexample. Here "row" means "row"; there, "row" means
   * cycle. However, not every "cycle-row" in the counterexample has a duration
   * @param row
   * @return
   */
  public ConcreteDuration getConcreteDurationForRow(int row) {
    return counterExample.get().getDuration(row);
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

  class ValidSpecificationChangedListener<T> implements ChangeListener<T> {
    @Override
    public void changed(ObservableValue<? extends T> observableValue, T t, T t1) {
      onValidSpecificationChanged();
    }
  }

  class ConcreteSpecificationChangedListener<T> implements ChangeListener<T> {
    @Override
    public void changed(ObservableValue<? extends T> observableValue, T t, T t1) {
      onConcreteSpecificationChanged();
    }
  }

}
