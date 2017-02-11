package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException;
import edu.kit.iti.formal.stvs.model.table.*;
import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.ReadOnlyObjectProperty;
import javafx.beans.property.SimpleObjectProperty;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by philipp on 09.02.17.
 */
public class SpecProblemRecognizer {

  private final ObjectProperty<List<SpecProblem>> problems;
  private final ObjectProperty<List<Type>> typeContext;
  private final ObjectProperty<List<CodeIoVariable>> codeIoVariables;
  private final ReadOnlyObjectProperty<List<ValidFreeVariable>> validFreeVariables;
  private final ConstraintSpecification specification;

  private final NullableProperty<ValidSpecification> validSpecification;

  private final InvalidationListener listenToSpecUpdate = this::onSpecUpdated;

  public SpecProblemRecognizer(
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

    // All these ObservableLists invoke the InvalidationListeners on deep updates
    // So if only a cell in the Specification changes, the change listener on the ObservableList
    // two layers above gets notified.
    specification.getRows().addListener(listenToSpecUpdate);
    specification.getDurations().addListener(listenToSpecUpdate);

    typeContext.addListener(listenToSpecUpdate);
    codeIoVariables.addListener(listenToSpecUpdate);

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
          expressionsForRow.put(columnId, expressionOrProblemForCell(typeChecker, columnId, rowIndex, cell));
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
            lowerBoundedIntervalOrProblemForDuration(durIndex, specification.getDurations().get(durIndex));
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
  }

  private LowerBoundedInterval lowerBoundedIntervalOrProblemForDuration(int row, ConstraintDuration duration)
      throws DurationProblem {
    try {
      return IntervalParser.parse(duration.getAsString());
    } catch (ParseException parseException) {
      throw new DurationParseProblem(parseException, row);
    }
  }

  private Expression expressionOrProblemForCell(TypeChecker typeChecker, String columnId, int row, ConstraintCell cell)
      throws CellProblem {
    try {
      return createValidExpressionFromCell(typeChecker, columnId, cell);
    } catch (TypeCheckException typeCheckException) {
      throw new CellTypeProblem(typeCheckException, columnId, row);
    } catch (ParseException parseException) {
      throw new CellParseProblem(parseException, columnId, row);
    } catch (UnsupportedExpressionException unsupportedException) {
      throw new CellUnsupportedExpressionProblem(unsupportedException, columnId, row);
    }
  }

  protected Expression createValidExpressionFromCell(TypeChecker typeChecker, String columnId, ConstraintCell cell)
      throws TypeCheckException, ParseException, UnsupportedExpressionException {
    // First try to parse the expression:
    ExpressionParser parser = new ExpressionParser(columnId, typeContext.get());
    Expression expression = parser.parseExpression(cell.getAsString());

    Type type = typeChecker.typeCheck(expression);
    if (type.checksAgainst(TypeBool.BOOL)) {
      return expression;
    } else {
      throw new TypeCheckException(expression,
          "The cell expression must evaluate to a boolean, instead it evaluates to: " + type.getTypeName());
    }
  }

}
