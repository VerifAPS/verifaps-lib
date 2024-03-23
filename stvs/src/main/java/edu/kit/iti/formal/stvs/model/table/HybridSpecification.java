package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;

/**
 * A {@link ConstraintSpecification} which also has an associated counterexample (a
 * {@link ConcreteSpecification}), a concrete instance ({@link ConcreteSpecification}) or both. This
 * class is the model on which the {@link edu.kit.iti.formal.stvs.view.spec.SpecificationController}
 * and {@link TimingDiagramCollectionController} operate.
 *
 * @author Benjamin Alt
 */
public class HybridSpecification extends ConstraintSpecification {

  private final NullableProperty<ConcreteSpecification> counterExample;
  private final NullableProperty<ConcreteSpecification> concreteInstance;
  private final boolean editable;
  private final ObservableList<HybridRow> rowsAsHybrid;

  /**
   * Stores which cell in the table is currently highlighted in the view. This is saved here in
   * order to allow the table and timing diagram to share the same reference.
   */
  private Selection selection;

  /**
   * Create a new, empty hybrid specification with a default name from a list of free variables.
   *
   * @param freeVariableList A list of initial free variables
   * @param editable True if this hybridSpecification is editable, false otherwise
   */
  public HybridSpecification(FreeVariableList freeVariableList, boolean editable) {
    this(DEFAULT_NAME, freeVariableList, editable);
  }

  /**
   * Create a new, empty hybrid specification with a given name and a list of free variables.
   *
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
    this.rowsAsHybrid = FXCollections.observableArrayList();
    rowsAsHybrid.addListener(this::onHybridRowChanged);
    counterExample.addListener(event -> onCounterExampleChanged());
  }

  /**
   * Create a HybridSpecification from a {@link ConstraintSpecification}.
   *
   * @param sourceSpec The original {@link ConstraintSpecification}
   * @param editable True if this HybridSpecification is editable, false otherwise
   */
  public HybridSpecification(ConstraintSpecification sourceSpec, boolean editable) {
    this(sourceSpec.getName(), sourceSpec.getFreeVariableList(), editable);
    getColumnHeaders().addAll(sourceSpec.getColumnHeaders());

    for (int rowIndex = 0; rowIndex < sourceSpec.getRows().size(); rowIndex++) {
      HybridRow row = new HybridRow(sourceSpec.getRows().get(rowIndex),
          sourceSpec.getDurations().get(rowIndex));
      row.updateCounterExampleCells(rowIndex, getCounterExample());
      rowsAsHybrid.add(row);
    }
  }

  private void onCounterExampleChanged() {
    for (int rowIndex = 0; rowIndex < getRows().size(); rowIndex++) {
      rowsAsHybrid.get(rowIndex).updateCounterExampleCells(rowIndex, getCounterExample());
    }
  }

  private void onHybridRowChanged(ListChangeListener.Change<? extends HybridRow> change) {
    while (change.next()) {
      if (change.wasAdded()) {
        List<SpecificationRow<ConstraintCell>> rowsToBeAdded = new ArrayList<>();
        List<ConstraintDuration> durationsToBeAdded = new ArrayList<>();
        for (HybridRow row : change.getAddedSubList()) {
          SpecificationRow<ConstraintCell> rowToBeAdded = row.getSourceRow();
          rowToBeAdded.commentProperty().bindBidirectional(row.commentProperty());
          rowsToBeAdded.add(rowToBeAdded);
          durationsToBeAdded.add(row.getDuration().getCell());
        }
        getRows().addAll(change.getFrom(), rowsToBeAdded);
        getDurations().addAll(change.getFrom(), durationsToBeAdded);
      }
      if (change.wasRemoved()) {
        getRows().remove(change.getFrom(), change.getFrom() + change.getRemovedSize());
        getDurations().remove(change.getFrom(), change.getFrom() + change.getRemovedSize());
      }
    }
  }

  public Optional<ConcreteSpecification> getCounterExample() {
    return Optional.ofNullable(counterExample.get());
  }

  /**
   * Sets the counterexample for this hybrid specification. This will automatically update
   * the {@link HybridRow}'s counterexample cells in {@link #getHybridRows()} from the given
   * counterexample.
   *
   * @param counterExample the concrete specification to be shown in-place in the gui
   * @throws IllegalArgumentException if the given concrete instance's column headers don't match
   *                                  this specification's column headers
   */
  public void setCounterExample(ConcreteSpecification counterExample) {
    if (counterExample != null) {
      if (!columnHeadersMatch(counterExample.columnHeaders)) {
        throw new IllegalArgumentException("The column headers of the concrete instance are not "
            + "compatible with this hybrid specification");
      }
      this.counterExample.set(counterExample);
    }
  }

  public ObservableList<HybridRow> getHybridRows() {
    return rowsAsHybrid;
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

  /**
   * <p>Set the generated concrete instance for this hybrid specification, that is the
   * concretized constraint specification. This is concrete instance is then used from
   * the {@link TimingDiagramCollectionController} to view a timing diagram.</p>
   *
   * @param concreteInstance the concretized constraint specification
   * @throws IllegalArgumentException if the given concrete instance's column headers don't match
   *                                  this specification's column headers
   */
  public void setConcreteInstance(ConcreteSpecification concreteInstance) {
    if (concreteInstance != null) {
      if (!columnHeadersMatch(concreteInstance.columnHeaders)) {
        throw new IllegalArgumentException("The column headers of the concrete instance are not "
            + "compatible with this hybrid specification");
      }
      this.concreteInstance.set(concreteInstance);
    }
  }

  private boolean columnHeadersMatch(ObservableList<ValidIoVariable> columnHeaders) {
    if (this.columnHeaders.size() != columnHeaders.size()) {
      return false;
    }
    for (int i = 0; i < this.columnHeaders.size(); i++) {
      if (!this.columnHeaders.get(i).matches(columnHeaders.get(i))) {
        return false;
      }
    }
    return true;
  }

  public void removeConcreteInstance() {
    concreteInstance.set(null);
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (getCounterExample() != null ? getCounterExample().hashCode() : 0);
    result = 31 * result + (getConcreteInstance() != null ? getConcreteInstance().hashCode() : 0);
    result = 31 * result + (isEditable() ? 1 : 0);
    result = 31 * result + (rowsAsHybrid != null ? rowsAsHybrid.hashCode() : 0);
    result = 31 * result + (getSelection() != null ? getSelection().hashCode() : 0);
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }
    if (!super.equals(obj)) {
      return false;
    }

    HybridSpecification that = (HybridSpecification) obj;

    if (isEditable() != that.isEditable()) {
      return false;
    }
    if (getCounterExample() != null ? !getCounterExample().equals(that.getCounterExample())
        : that.getCounterExample() != null) {
      return false;
    }
    if (getConcreteInstance() != null ? !getConcreteInstance().equals(that.getConcreteInstance())
        : that.getConcreteInstance() != null) {
      return false;
    }
    if (rowsAsHybrid != null ? !rowsAsHybrid.equals(that.rowsAsHybrid)
        : that.rowsAsHybrid != null) {
      return false;
    }
    return getSelection() != null ? getSelection().equals(that.getSelection())
        : that.getSelection() == null;
  }
}
