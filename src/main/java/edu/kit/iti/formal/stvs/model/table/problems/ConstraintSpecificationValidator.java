package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by philipp on 09.02.17.
 *
 * @author Philipp
 */
public class ConstraintSpecificationValidator {

  private final ObjectProperty<List<SpecProblem>> problems;
  private final ObjectProperty<List<Type>> typeContext;
  private final ObjectProperty<List<CodeIoVariable>> codeIoVariables;
  private final ReadOnlyObjectProperty<List<ValidFreeVariable>> validFreeVariables;
  private final ConstraintSpecification specification;
  private final BooleanProperty valid;

  private final NullableProperty<ValidSpecification> validSpecification;

  private final InvalidationListener listenToSpecUpdate = this::onSpecUpdated;

  public ConstraintSpecificationValidator(
      ObjectProperty<List<Type>> typeContext,
      ObjectProperty<List<CodeIoVariable>> codeIoVariables,
      ReadOnlyObjectProperty<List<ValidFreeVariable>> validFreeVariables,
      ConstraintSpecification specification) {
    this.typeContext = typeContext;
    this.codeIoVariables = codeIoVariables;
    this.validFreeVariables = validFreeVariables;
    this.specification = specification;

    this.problems = new SimpleObjectProperty<>(new ArrayList<>());
    this.validSpecification = new NullableProperty<>();
    this.valid = new SimpleBooleanProperty(false);

    // All these ObservableLists invoke the InvalidationListeners on deep updates
    // So if only a cell in the Specification changes, the change listener on the ObservableList
    // two layers above gets notified.
    specification.getRows().addListener(listenToSpecUpdate);
    specification.getDurations().addListener(listenToSpecUpdate);
    specification.getColumnHeaders().addListener(listenToSpecUpdate);

    typeContext.addListener(listenToSpecUpdate);
    codeIoVariables.addListener(listenToSpecUpdate);
    validFreeVariables.addListener(listenToSpecUpdate);

    recalculateSpecProblems();
  }

  public ObjectProperty<List<SpecProblem>> problemsProperty() {
    return problems;
  }

  private void onSpecUpdated(Observable observable) {
    recalculateSpecProblems();
  }

  private void recalculateSpecProblems() {
    ValidSpecification validSpec = new ValidSpecification();

    List<SpecProblem> specProblems = new ArrayList<>();

    boolean specificationIsValid = true;

    Map<String, Type> variableTypes = validFreeVariables.get().stream()
        .collect(Collectors.toMap(ValidFreeVariable::getName, ValidFreeVariable::getType));

    Map<String, Type> typesByName = typeContext.get().stream()
        .collect(Collectors.toMap(Type::getTypeName, Function.identity()));

    for (SpecIoVariable specIoVariable : specification.getColumnHeaders()) {
      // Check column header for problem
      try {
        ValidIoVariable validIoVariable = InvalidIoVarProblem.tryGetValidIoVariable(
            specIoVariable,
            codeIoVariables.get(),
            typesByName,
            specProblems::add); // On non-fatal problems (like missing matching CodeIoVariable)
        variableTypes.put(validIoVariable.getName(), validIoVariable.getValidType());
        if (specificationIsValid) {
          validSpec.getColumnHeaders().add(validIoVariable);
        }
      } catch (InvalidIoVarProblem invalidIoVarProblem) { // Fatal problem (like invalid type, etc)
        specificationIsValid = false;
        specProblems.add(invalidIoVarProblem);
      }
    }

    TypeChecker typeChecker = new TypeChecker(variableTypes);

    for (int rowIndex = 0; rowIndex < specification.getRows().size(); rowIndex++) {
      SpecificationRow<ConstraintCell> row = specification.getRows().get(rowIndex);

      Map<String, Expression> expressionsForRow = new HashMap<>();

      // Check cells for problems
      for (Map.Entry<String, ConstraintCell> mapEntry : row.getCells().entrySet()) {
        String columnId = mapEntry.getKey();
        ConstraintCell cell = mapEntry.getValue();

        try {
          expressionsForRow.put(columnId,
              CellParseProblem.expressionOrProblemForCell(
                  typeContext.get(), typeChecker, columnId, rowIndex, cell));
        } catch (CellProblem problem) {
          specProblems.add(problem);
          specificationIsValid = false;
        }
      }

      // Fixes a dumb bug with listeners getting invoked midst column adding
      if (specificationIsValid && expressionsForRow.size() == validSpec.getColumnHeaders().size()) {
        validSpec.getRows().add(SpecificationRow.createUnobservableRow(expressionsForRow));
      } else {
        specificationIsValid = false;
      }
    }

    for (int durIndex = 0; durIndex < specification.getDurations().size(); durIndex++) {
      try {
        LowerBoundedInterval interval =
            DurationProblem.tryParseDuration(durIndex, specification.getDurations().get(durIndex));
        if (specificationIsValid) {
          validSpec.getDurations().add(interval);
        }
      } catch (DurationProblem problem) {
        specProblems.add(problem);
        specificationIsValid = false;
      }
    }

    this.problems.set(specProblems);

    if (specificationIsValid) {
      validSpecification.set(validSpec);
    } else {
      validSpecification.set(null);
    }
    valid.set(specProblems.isEmpty());
  }

  public ReadOnlyBooleanProperty validProperty() {
    return valid;
  }

  public ValidSpecification getValidSpecification() {
    return validSpecification.get();
  }

  public NullableProperty<ValidSpecification> validSpecificationProperty() {
    return validSpecification;
  }

}
