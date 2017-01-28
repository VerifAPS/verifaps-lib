package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.logic.specification.BacktrackSpecificationConcretizer;
import edu.kit.iti.formal.stvs.logic.specification.ConcretizerContext;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

/**
 * A ConstraintSpecification which also has an associated counterexample (ConcreteSpecification),
 * concrete instance (ConcreteSpecification) or both.
 * This class is the model on which the
 * {@link edu.kit.iti.formal.stvs.view.spec.table.TablePaneController}
 * and {@link edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController}
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
   * @param typeContext The type context (which types exist?)
   * @param ioVariables The IO variables declared in the code
   * @param freeVariableSet The set of declared free variables
   * @param editable Is this HybridSpecification supposed to be editable?
   */
  public HybridSpecification(Set<Type> typeContext, Set<CodeIoVariable> ioVariables,
                             FreeVariableSet freeVariableSet, boolean editable) {
    super(typeContext, ioVariables, freeVariableSet);
    this.editable = editable;
    initialize();
  }

  /**
   * Constructor for a HybridSpecification that already contains some cells.
   * @param columns The columns of the specification
   * @param durations The durations for the specification
   * @param typeContext The type context (which types exist?)
   * @param ioVariables The IO variables declared in the code
   * @param freeVariableSet The set of declared free variables
   * @param editable Is this HybridSpecification supposed to be editable?
   */
  public HybridSpecification(Map<String, SpecificationColumn<ConstraintCell>> columns,
                             Map<Integer,ConstraintDuration> durations, Set<Type> typeContext,
                             Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet,
                             boolean editable) {
    super(columns, durations, typeContext, ioVariables, freeVariableSet);
    this.editable = editable;
    initialize();
  }

  private void initialize() {
    this.selection = new Selection();
    concreteInstance = new OptionalProperty<>(new SimpleObjectProperty<>());
    validSpecificationProperty().addListener(new ValidSpecificationChangedListener<>());
    concretizer = new BacktrackSpecificationConcretizer(new ConcretizerContext());
    concretizer.concreteSpecProperty().addListener(new ConcreteSpecificationChangedListener<>());
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

  /* TODO: This was not specified originally, but it would not make sense for the selection to be
     read-only */
  public void setSelection(Selection selection) {
    this.selection = selection;
  }

  /**
   *
   * For the counterexample.
   * A row in a ConcreteSpecification is not the same as a row in a ConstraintSpecification.
   * This function does the mapping between the two.
   * TODO: Should we move this method into ConcreteSpecification? It seems artificial to keep it here.
   */
  public List<ConcreteCell> getConcreteValuesForConstraint(String column, int row) {
    if (counterExample != null) {
      int startIndex = counterExample.getDuration(row).getBeginCycle();
      int endIndex = counterExample.getDuration(row).getEndCycle();
      ArrayList<ConcreteCell> concreteCells = new ArrayList<>();
      for (int i = startIndex; i < endIndex; i++) {
        concreteCells.add(counterExample.getCell(i, column));
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
     if (counterExample != null) {
       return counterExample.getDuration(row);
     } else {
       return null;
     }
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
