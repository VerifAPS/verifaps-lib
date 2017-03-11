package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;

/**
 * The validator for {@link ConstraintSpecification}s. It converts these into the formal model:
 * {@link ValidSpecification}. If there are any problems while converting, then {@link SpecProblem}s
 * are created. This object has observable properties and can therefore be used like any other model
 * instance in the controllers.
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

  /**
   * <p>
   * Creates a validator with given observable models as context information.
   * </p>
   *
   * <p>
   * The validator observes changes in any of the given context models. It automatically updates the
   * validated specification (see {@link #validSpecificationProperty()}) and/or the problems with
   * the constraint specification (see {@link #problemsProperty()}).
   * </p>
   *
   * @param typeContext the extracted types (esp. enums) from the code area
   * @param codeIoVariables the extracted {@link CodeIoVariable}s from the code area
   * @param validFreeVariables the most latest validated free variables from the
   *        {@link FreeVariableList}.
   * @param specification the specification to be validated
   */
  public ConstraintSpecificationValidator(ObjectProperty<List<Type>> typeContext,
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

  /**
   * <p>
   * Tries to create an {@link Expression}-AST from the given {@link ConstraintCell} that has the
   * correct type using context information (for example like a type context).
   * </p>
   *
   * @param typeContext the type context to use for parsing the cell (needed for encountering enum
   *        values)
   * @param typeChecker the type checker instance for insuring the correct type
   * @param columnId the name of the column for parsing single-sided expressions like "> 3"
   * @param row the row for better error messages
   * @param cell the cell to be validated
   * @return the AST as {@link Expression} that is fully type-correct.
   * @throws CellProblem if the cell could not be parsed ({@link CellParseProblem}) or if the cell
   *         is ill-typed ({@link CellTypeProblem}).
   */
  public static Expression tryValidateCellExpression(List<Type> typeContext,
      TypeChecker typeChecker, String columnId, int row, ConstraintCell cell) throws CellProblem {
    Expression expr = CellParseProblem.tryParseCellExpression(typeContext, columnId, row, cell);
    return CellTypeProblem.tryTypeCheckCellExpression(typeChecker, columnId, row, expr);
  }

  public ObjectProperty<List<SpecProblem>> problemsProperty() {
    return problems;
  }

  private void onSpecUpdated(Observable observable) {
    recalculateSpecProblems();
  }


  /**
   * Calculates the problems of the specification table.
   */
  public void recalculateSpecProblems() {
    ValidSpecification validSpec = new ValidSpecification();

    List<SpecProblem> minorSpecProblems = new ArrayList<>();
    List<SpecProblem> majorSpecProblems = new ArrayList<>();

    boolean specificationIsValid;

    Map<String, Type> typesByName = typeContext.get().stream()
        .collect(Collectors.toMap(Type::getTypeName, Function.identity()));

    specificationIsValid =
        areCellsValid(validSpec, minorSpecProblems, majorSpecProblems, typesByName);

    specificationIsValid = areDurationsValid(validSpec, majorSpecProblems, specificationIsValid);

    ArrayList<SpecProblem> specProblems = new ArrayList<>();
    specProblems.addAll(minorSpecProblems);
    specProblems.addAll(majorSpecProblems);
    this.problems.set(specProblems);

    if (specificationIsValid) {
      validSpecification.set(validSpec);
    } else {
      validSpecification.set(null);
    }
    valid.set(minorSpecProblems.isEmpty());
  }

  /**
   * Calculates if durations are valid. Durations are never valid if the given specification is
   * invalid. Therefore {@code specificationIsValid == false} => {@code areDurationsValid(...)} ==
   * false}. Any found problem is added to {@code specProblems}.
   * 
   * @param validSpec specification that should be checked
   * @param majorSpecProblems List of major problems
   * @param specificationIsValid does the given specification valid seem to be valid?
   * @return returns if durations are valid
   */
  private boolean areDurationsValid(ValidSpecification validSpec,
      List<SpecProblem> majorSpecProblems, boolean specificationIsValid) {
    for (int durIndex = 0; durIndex < specification.getDurations().size(); durIndex++) {
      try {
        LowerBoundedInterval interval = DurationParseProblem.tryParseDuration(durIndex,
            specification.getDurations().get(durIndex));
        if (specificationIsValid) {
          validSpec.getDurations().add(interval);
        }
      } catch (DurationProblem problem) {
        majorSpecProblems.add(problem);
        specificationIsValid = false;
      }
    }
    return specificationIsValid;
  }

  /**
   * Calculates if cells are valid. Any found problem is added to {@code minorSpecProblems}.
   * 
   * @param validSpec specification that should be checked
   * @param minorSpecProblems List of noticeable problems
   * @param majorSpecProblems List of fatal problems
   * @param typesByName map of types found in the specification
   * @return returns if cells are valid
   */
  private boolean areCellsValid(ValidSpecification validSpec, List<SpecProblem> minorSpecProblems,
      List<SpecProblem> majorSpecProblems, Map<String, Type> typesByName) {
    Map<String, Type> variableTypes =
        createVariableTypes(validSpec, minorSpecProblems, majorSpecProblems, typesByName);
    TypeChecker typeChecker = new TypeChecker(variableTypes);
    boolean specificationIsValid = true;

    for (int rowIndex = 0; rowIndex < specification.getRows().size(); rowIndex++) {
      SpecificationRow<ConstraintCell> row = specification.getRows().get(rowIndex);

      Map<String, Expression> expressionsForRow = new HashMap<>();

      // Check cells for problems
      for (Map.Entry<String, ConstraintCell> mapEntry : row.getCells().entrySet()) {
        String columnId = mapEntry.getKey();
        ConstraintCell cell = mapEntry.getValue();

        try {
          expressionsForRow.put(columnId,
              tryValidateCellExpression(typeContext.get(), typeChecker, columnId, rowIndex, cell));
        } catch (CellProblem problem) {
          majorSpecProblems.add(problem);
        }
      }

      specificationIsValid = majorSpecProblems.isEmpty() && specificationIsValid;

      // Fixes a dumb bug with listeners getting invoked midst column adding
      if (specificationIsValid && expressionsForRow.size() == validSpec.getColumnHeaders().size()) {
        validSpec.getRows().add(SpecificationRow.createUnobservableRow(expressionsForRow));
      } else {
        specificationIsValid = false;
      }
    }
    return specificationIsValid;
  }

  /**
   * Extracts variable types from specification. Any found problem is added to {@code specProblems}.
   * 
   * @param validSpec specification that contains the variables
   * @param minorSpecProblems List of noticeable problems
   * @param majorSpecProblems List of fatal problems
   * @param typesByName map of types found in the specification @return returns map of variable
   *        types
   */
  private Map<String, Type> createVariableTypes(ValidSpecification validSpec,
      List<SpecProblem> minorSpecProblems, List<SpecProblem> majorSpecProblems,
      Map<String, Type> typesByName) {
    Map<String, Type> variableTypes = validFreeVariables.get().stream()
        .collect(Collectors.toMap(ValidFreeVariable::getName, ValidFreeVariable::getType));

    for (SpecIoVariable specIoVariable : specification.getColumnHeaders()) {
      // Check column header for problem
      try {
        // On non-fatal problems (like missing matching CodeIoVariable)
        // minorSpecProblems::add is called:
        ValidIoVariable validIoVariable = InvalidIoVarProblem.tryGetValidIoVariable(specIoVariable,
            codeIoVariables.get(), typesByName, minorSpecProblems::add);
        variableTypes.put(validIoVariable.getName(), validIoVariable.getValidType());
        if (majorSpecProblems.isEmpty()) {
          validSpec.getColumnHeaders().add(validIoVariable);
        }
      } catch (InvalidIoVarProblem invalidIoVarProblem) { // Fatal problem (like invalid type, etc)
        majorSpecProblems.add(invalidIoVarProblem);
      }
    }
    return variableTypes;
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
